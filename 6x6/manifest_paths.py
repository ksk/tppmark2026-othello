"""Resolve build inputs relative to a certificate manifest within 6x6/."""
from pathlib import Path


def resolve_path(manifest_directory, value):
    directory = Path(manifest_directory).resolve()
    path = Path(value)
    if path.is_absolute():
        raise ValueError(f'Manifest build paths must be relative: {value}')
    resolved = (directory / path).resolve()
    if not resolved.is_relative_to(directory.parent):
        raise ValueError(f'Manifest build path leaves the certificate tree: {value}')
    return resolved
