"""Optimal socialnetwork suites: python minimal/socialnetwork.py R [n]."""

import sys

from benchmarks import SOCIAL
from optimal import *  # Retain the original socialnetwork.py Python API.
from optimal import main as run, parse_args as arguments


def parse_args(argv=None):
    return arguments(argv, SOCIAL)


def main(argv=None):
    return run(argv, SOCIAL)


if __name__ == "__main__":
    sys.exit(main())
