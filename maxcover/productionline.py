"""Optimal productionline suites: python minimal/productionline.py R [n]."""

import sys

from benchmarks import PRODUCTION
from optimal import main as run, parse_args as arguments


def parse_args(argv=None):
    return arguments(argv, PRODUCTION)


def main(argv=None):
    return run(argv, PRODUCTION)


if __name__ == "__main__":
    sys.exit(main())
