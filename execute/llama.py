"""Compatibility entry point; use generate.py --model for new experiments."""

import sys

if __package__:
    from .generate import main
else:
    from generate import main


if __name__ == "__main__":
    sys.exit(main(default_model="llama3.1:8b"))
