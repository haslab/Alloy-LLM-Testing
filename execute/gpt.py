"""Compatibility entry point; use generate.py --model for new experiments."""

import sys

if __package__:
    from .generate import main
else:
    from generate import main


if __name__ == "__main__":
    sys.exit(main(default_model="gpt-5-2025-08-07"))
