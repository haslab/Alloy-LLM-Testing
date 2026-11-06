"""Provider selection and model calls for the instance-generation experiment."""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import uuid
from dataclasses import dataclass
from pathlib import Path


PLATFORMS = ("gpt-api", "claude-api", "gemini-api", "deepseek-api", "ollama", "codex-cli")
MODEL_PREFIXES = {
    "openai/": "gpt-api",
    "anthropic/": "claude-api",
    "google/": "gemini-api",
    "models/": "gemini-api",
    "deepseek/": "deepseek-api",
    "ollama/": "ollama",
}


@dataclass(frozen=True)
class ModelResponse:
    text: str
    input_tokens: int = 0
    output_tokens: int = 0
    cached_input_tokens: int = 0


class CacheUsageError(RuntimeError):
    """A response reported cached tokens, so the experiment must stop."""


def require_no_cache_usage(platform: str, model: str, **token_counts) -> None:
    reported = {name: count for name, count in token_counts.items() if (count or 0) > 0}
    if reported:
        details = ", ".join(f"{name}={count}" for name, count in reported.items())
        raise CacheUsageError(
            f"{platform} model '{model}' reported prompt cache usage ({details}). "
            "Stopping the experiment."
        )


def _usage_field(usage, name: str):
    # Older SDKs can retain newer response fields as untyped dictionaries.
    return usage.get(name) if isinstance(usage, dict) else getattr(usage, name, None)


def infer_platform(model: str) -> str:
    """Infer a transport, leaving unfamiliar model names to an explicit override."""
    name = model.strip().lower()
    if not name:
        raise ValueError("The model ID must not be empty.")
    for prefix, platform in MODEL_PREFIXES.items():
        if name.startswith(prefix):
            return platform
    if ":" in name or name.startswith("llama"):
        return "ollama"
    if name.startswith(("gpt-", "chatgpt-", "codex")) or re.match(r"^o\d", name):
        return "gpt-api"
    if name.startswith("claude"):
        return "claude-api"
    if name.startswith("gemini"):
        return "gemini-api"
    if name.startswith("deepseek"):
        return "deepseek-api"
    raise ValueError(f"Cannot infer the API for model '{model}'. Pass --platform explicitly.")


def resolve_model_id(model: str, platform: str) -> str:
    """Remove a provider namespace only when it belongs to the chosen transport."""
    name = model.strip()
    if not name:
        raise ValueError("The model ID must not be empty.")
    for prefix, provider in MODEL_PREFIXES.items():
        if name.lower().startswith(prefix) and (
            provider == platform or (provider == "gpt-api" and platform == "codex-cli")
        ):
            name = name[len(prefix):]
            break
    if not name:
        raise ValueError("The model ID must not be empty after its provider prefix.")
    return name


def resolve_codex_exec(value: str) -> str:
    """Find the CLI on PATH, in an explicit location, or in a macOS app bundle."""
    executable = Path(value).expanduser()
    if executable.suffix == ".app":
        apps = [executable]
    else:
        if executable.is_file():
            return str(executable.resolve())
        found = shutil.which(str(executable))
        if found:
            return str(Path(found).resolve())
        if value != "codex" or sys.platform != "darwin":
            return str(executable)
        apps = [
            folder / name
            for folder in (Path("/Applications"), Path.home() / "Applications")
            for name in ("ChatGPT.app", "Codex.app")
        ]
    for app in apps:
        for relative in (
            "Contents/Resources/codex-cli/CodexCLI.app/Contents/MacOS/codex",
            "Contents/Resources/codex-cli/bin/codex",
            "Contents/Resources/codex",
            "Contents/MacOS/codex",
        ):
            candidate = app / relative
            if candidate.is_file() and os.access(candidate, os.X_OK):
                return str(candidate.resolve())
    return str(executable)


class ModelClient:
    """Lazily load only the SDK needed for the selected model."""

    def __init__(self, model: str, platform: str | None = None, codex_exec: str = "codex"):
        self.platform = platform or infer_platform(model)
        if self.platform not in PLATFORMS:
            raise ValueError(f"Unsupported platform: {self.platform}")
        self.model = resolve_model_id(model, self.platform)
        self.codex_exec = resolve_codex_exec(codex_exec)
        self._client = None

    def call(self, system_prompt: str, task: str, *, response_format=None) -> ModelResponse:
        adapters = {
            "gpt-api": self._call_gpt,
            "claude-api": self._call_claude,
            "gemini-api": self._call_gemini,
            "deepseek-api": self._call_deepseek,
            "ollama": self._call_ollama,
            "codex-cli": self._call_codex,
        }
        if response_format is not None and self.platform != "ollama":
            raise ValueError("Native response_format is currently supported only by the Ollama adapter.")
        try:
            options = {"response_format": response_format} if response_format is not None else {}
            response = adapters[self.platform](system_prompt, task, **options)
        except ImportError as exc:
            raise RuntimeError(
                f"Missing dependency for {self.platform}. Install requirements.txt "
                "or the SDK for this provider."
            ) from exc
        if not response.text or not response.text.strip():
            raise RuntimeError(f"{self.platform} returned no text content.")
        return response

    def _call_gpt(self, system_prompt: str, task: str) -> ModelResponse:
        if self._client is None:
            from openai import OpenAI

            self._client = OpenAI()
        response = self._client.responses.create(
            model=self.model, instructions=system_prompt, input=task,
            # Explicit mode without breakpoints disables cache reads and writes
            # on GPT-5.6 and later. extra_body also works with the pinned SDK.
            extra_body={"prompt_cache_options": {"mode": "explicit"}},
        )
        usage = response.usage
        details = _usage_field(usage, "input_tokens_details")
        writes = _usage_field(details, "cache_write_tokens_details")
        require_no_cache_usage(
            self.platform, self.model,
            cached_tokens=_usage_field(details, "cached_tokens"),
            cache_write_tokens=_usage_field(details, "cache_write_tokens"),
            ttl_30m_tokens=_usage_field(writes, "ttl_30m_tokens"),
            ttl_12h_tokens=_usage_field(writes, "ttl_12h_tokens"),
        )
        if response.status != "completed":
            raise RuntimeError(f"OpenAI response did not complete: {response.status}")
        return ModelResponse(
            response.output_text,
            getattr(usage, "input_tokens", 0) or 0,
            getattr(usage, "output_tokens", 0) or 0,
        )

    def _call_claude(self, system_prompt: str, task: str) -> ModelResponse:
        if self._client is None:
            import anthropic

            self._client = anthropic.Anthropic(timeout=1000.0)
        # Preserve the original experiment's sampling for the older Claude models.
        # Newer models reject non-default sampling parameters.
        sampling = {}
        if self.model.startswith("claude-3") or re.match(
            r"^claude-(?:opus|sonnet|haiku)-4-[0-6](?:-|$)", self.model
        ):
            sampling["temperature"] = 0
        # Claude Messages caching is opt-in. Keep cache_control absent both at
        # the top level and on content blocks so requests use no prompt caching.
        response = self._client.messages.create(
            model=self.model,
            max_tokens=20000,
            system=system_prompt,
            messages=[{"role": "user", "content": task}],
            **sampling,
        )
        usage = response.usage
        creation = _usage_field(usage, "cache_creation")
        require_no_cache_usage(
            self.platform, self.model,
            cache_read_input_tokens=_usage_field(usage, "cache_read_input_tokens"),
            cache_creation_input_tokens=_usage_field(usage, "cache_creation_input_tokens"),
            ephemeral_5m_input_tokens=_usage_field(creation, "ephemeral_5m_input_tokens"),
            ephemeral_1h_input_tokens=_usage_field(creation, "ephemeral_1h_input_tokens"),
        )
        if response.stop_reason != "end_turn":
            raise RuntimeError(f"Claude response did not complete: {response.stop_reason}")
        text = "\n".join(block.text for block in response.content if block.type == "text")
        return ModelResponse(text, usage.input_tokens, usage.output_tokens)

    def _call_gemini(self, system_prompt: str, task: str) -> ModelResponse:
        from google import genai
        from google.genai import types

        if self._client is None:
            self._client = genai.Client()
        response = self._client.models.generate_content(
            model=self.model,
            config=types.GenerateContentConfig(
                system_instruction=system_prompt, temperature=0, seed=0,
            ),
            contents=task,
        )
        usage = response.usage_metadata
        require_no_cache_usage(
            self.platform, self.model,
            cached_content_token_count=_usage_field(usage, "cached_content_token_count"),
        )
        if response.candidates and response.candidates[0].finish_reason != "STOP":
            raise RuntimeError(
                f"Gemini response did not complete: {response.candidates[0].finish_reason}"
            )
        return ModelResponse(
            response.text,
            getattr(usage, "prompt_token_count", 0) or 0,
            (getattr(usage, "candidates_token_count", 0) or 0)
            + (getattr(usage, "thoughts_token_count", 0) or 0),
        )

    def _call_deepseek(self, system_prompt: str, task: str) -> ModelResponse:
        if self._client is None:
            from openai import OpenAI

            api_key = os.environ.get("DEEPSEEK_API_KEY")
            if not api_key or not api_key.strip():
                raise RuntimeError("Set DEEPSEEK_API_KEY to use the DeepSeek API.")
            # The runner handles retries so every attempt gets a fresh cache
            # namespace, including after a timeout with a potentially cached result.
            self._client = OpenAI(
                api_key=api_key, base_url="https://api.deepseek.com", max_retries=0,
            )
        response = self._client.chat.completions.create(
            model=self.model,
            messages=[{"role": "system", "content": system_prompt},
                      {"role": "user", "content": task}],
            temperature=0,
            # DeepSeek has no cache-off switch. A unique user_id isolates KVCache
            # for each request without changing the experiment's prompts.
            # https://api-docs.deepseek.com/quick_start/rate_limit/
            extra_body={"user_id": uuid.uuid4().hex},
        )
        usage = response.usage
        details = _usage_field(usage, "prompt_tokens_details")
        require_no_cache_usage(
            self.platform, self.model,
            prompt_cache_hit_tokens=_usage_field(usage, "prompt_cache_hit_tokens"),
            cached_tokens=_usage_field(details, "cached_tokens"),
        )
        if not response.choices:
            raise RuntimeError("DeepSeek returned no response choices.")
        choice = response.choices[0]
        if choice.finish_reason != "stop":
            raise RuntimeError(f"DeepSeek response did not complete: {choice.finish_reason}")
        return ModelResponse(
            choice.message.content,
            _usage_field(usage, "prompt_tokens") or 0,
            # completion_tokens already includes reasoning tokens.
            _usage_field(usage, "completion_tokens") or 0,
        )

    def _call_ollama(self, system_prompt: str, task: str, *, response_format=None) -> ModelResponse:
        if self._client is None:
            from ollama import Client

            self._client = Client()
        options = {"format": response_format} if response_format is not None else {}
        response = self._client.generate(model=self.model, system=system_prompt, prompt=task, **options)
        return ModelResponse(
            response.response,
            response.prompt_eval_count or 0,
            response.eval_count or 0,
        )

    def _call_codex(self, system_prompt: str, task: str) -> ModelResponse:
        prompt = (
            "You are being used as a non-interactive model backend for an Alloy experiment.\n"
            "Follow the system instructions and answer the user task below. Return only "
            "the assistant response. Do not inspect or edit files, run commands, use tools, "
            "or include progress commentary.\n\n"
            f"SYSTEM INSTRUCTIONS:\n{system_prompt}\n\nUSER TASK:\n{task}"
        )
        env = os.environ.copy()
        # Subscription mode must not silently switch to API-key billing.
        env.pop("OPENAI_API_KEY", None)
        env.pop("CODEX_API_KEY", None)
        # A fresh directory avoids loading this project's files and instructions.
        with tempfile.TemporaryDirectory(prefix="alloy_codex_") as workdir:
            output = Path(workdir) / "response.txt"
            command = [
                self.codex_exec, "exec", "--ephemeral", "--skip-git-repo-check",
                "--sandbox", "read-only", "--color", "never", "--json",
                "-c", 'forced_login_method="chatgpt"',
                "-c", 'model_provider="openai"',
                "--output-last-message", str(output), "--model", self.model, "-",
            ]
            try:
                process = subprocess.run(
                    command, input=prompt, capture_output=True, text=True, cwd=workdir, env=env,
                )
            except FileNotFoundError as exc:
                raise RuntimeError(
                    f"Cannot find Codex CLI '{self.codex_exec}'. Install it or pass --codex-exec."
                ) from exc
            if process.returncode:
                raise RuntimeError(
                    "Codex CLI failed. Sign in with ChatGPT using 'codex login' and "
                    f"check that your plan supports model '{self.model}'.\n{process.stderr.strip()}"
                )
            usage = {}
            failure = None
            for line in process.stdout.splitlines():
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if event.get("type") == "turn.completed":
                    usage = event.get("usage") or {}
                    cached_tokens = usage.get("cached_input_tokens") or 0
                    if cached_tokens > 0:
                        print(
                            f"codex-cli model '{self.model}' reported "
                            f"cached_input_tokens={cached_tokens}. Continuing the experiment.",
                            file=sys.stderr,
                        )
                elif event.get("type") in ("turn.failed", "error"):
                    failure = event.get("error") or event.get("message") or event
            if failure:
                raise RuntimeError(f"Codex CLI turn failed: {failure}")
            if not output.is_file():
                raise RuntimeError("Codex CLI did not write a final response.")
            return ModelResponse(
                output.read_text(encoding="utf-8").strip(),
                usage.get("input_tokens") or 0,
                usage.get("output_tokens") or 0,
                usage.get("cached_input_tokens") or 0,
            )
