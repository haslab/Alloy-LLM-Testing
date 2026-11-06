"""Optimal courses suites: python minimal/courses.py R [n]."""

import sys

from benchmarks import COURSES
from optimal import main as run, parse_args as arguments


def parse_args(argv=None):
    return arguments(argv, COURSES)


def main(argv=None):
    return run(argv, COURSES)


if __name__ == "__main__":
    sys.exit(main())
