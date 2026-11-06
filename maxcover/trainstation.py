"""Optimal trainstation suites: python minimal/trainstation.py R [n]."""

import sys

from benchmarks import TRAIN
from optimal import main as run, parse_args as arguments


def parse_args(argv=None):
    return arguments(argv, TRAIN)


def main(argv=None):
    return run(argv, TRAIN)


if __name__ == "__main__":
    sys.exit(main())
