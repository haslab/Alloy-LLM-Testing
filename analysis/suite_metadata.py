"""Read requested suite counts independently of the generated output."""

from pathlib import Path
import re


def filename_counts(path):
    name = Path(path).stem
    match = re.search(r"_(\d+)pos-(\d+)neg(?:_|$)", name)
    if match:
        return tuple(map(int, match.groups()))
    match = re.search(r"_(?:few|one|zero)(\d+)(?:_|$)", name)
    return (int(match[1]), int(match[1])) if match else None


def requested_n(requirement, path):
    """Prefer generation settings/targets; return (n, filename_fallback_used)."""
    generation = requirement.get("generation", {})
    settings = generation.get("settings", {})
    count = settings.get("instances")
    if "instances" in settings and (type(count) is not int or count < 1):
        raise ValueError("generation.settings.instances must be a positive integer.")
    targets = generation.get("targets")
    target_count = None
    if targets is not None:
        if not isinstance(targets, dict):
            raise ValueError("generation.targets must record positive and negative slots.")
        positive, negative = targets.get("positive"), targets.get("negative")
        if (not isinstance(positive, list) or not isinstance(negative, list)
                or not positive or positive != negative
                or any(type(slot) is not int for slot in positive)
                or positive != list(range(1, len(positive) + 1))):
            raise ValueError("generation.targets must request the same numbered slots in both classifications.")
        target_count = len(positive)
    if count is not None:
        if target_count is not None and count != target_count:
            raise ValueError("Requested count disagrees with generation.targets.")
        return count, False
    if target_count is not None:
        return target_count, False
    counts = filename_counts(path)
    if counts is not None and counts[0] == counts[1] and counts[0] > 0:
        return counts[0], True
    return None, False


def complete_suite(n, generated, positives, negatives, valid):
    return n is not None and positives == negatives == n and generated == valid == 2 * n
