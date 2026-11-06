"""DeepSeek entry point; use --model to select another DeepSeek model."""

import sys

if __package__:
    from .generate import main
else:
    from generate import main


if __name__ == "__main__":
    sys.exit(main(default_model="deepseek-flash"))
