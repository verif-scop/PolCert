#!/usr/bin/env python3
from __future__ import annotations

from run_regression_suite import check_build_provenance


COMMIT = "a" * 40
SOURCE_SHA256 = "b" * 64
IMAGE_SHA256 = "c" * 64
PLUTO_COMMIT = "d" * 40
PLUTO_BUGGY_COMMIT = "e" * 40


def valid_environment() -> dict[str, str]:
    return {
        "POLCERT_REQUIRE_PROVENANCE": "1",
        "POLCERT_GIT_COMMIT": COMMIT,
        "POLCERT_RELEASE_TAG": "state-eq-v6",
        "POLCERT_SOURCE_ARCHIVE_SHA256": SOURCE_SHA256,
        "PLUTO_GIT_COMMIT": PLUTO_COMMIT,
        "PLUTO_BUGGY_GIT_COMMIT": PLUTO_BUGGY_COMMIT,
        "POLCERT_IMAGE_DIGEST": f"sha256:{IMAGE_SHA256}",
    }


def valid_manifest() -> dict[str, object]:
    return {
        "polcert_git_commit": COMMIT,
        "polcert_release_tag": "state-eq-v6",
        "polcert_source_archive_sha256": SOURCE_SHA256,
        "pluto_git_commit": PLUTO_COMMIT,
        "pluto_buggy_git_commit": PLUTO_BUGGY_COMMIT,
    }


def main() -> int:
    environment = valid_environment()
    manifest = valid_manifest()
    assert check_build_provenance(environment, manifest) == []

    environment["POLCERT_IMAGE_DIGEST"] = (
        f"registry.example/polcert@sha256:{IMAGE_SHA256}"
    )
    assert check_build_provenance(environment, manifest) == []

    for invalid_digest in ("", "unknown", "garbage", "sha256:1234"):
        environment["POLCERT_IMAGE_DIGEST"] = invalid_digest
        assert "invalid release environment field: POLCERT_IMAGE_DIGEST" in (
            check_build_provenance(environment, manifest)
        )

    environment = valid_environment()
    environment["PLUTO_GIT_COMMIT"] = "f" * 40
    assert "provenance mismatch: pluto_git_commit != PLUTO_GIT_COMMIT" in (
        check_build_provenance(environment, manifest)
    )

    environment = valid_environment()
    environment["PLUTO_BUGGY_GIT_COMMIT"] = "f" * 40
    assert (
        "provenance mismatch: pluto_buggy_git_commit != PLUTO_BUGGY_GIT_COMMIT"
        in check_build_provenance(environment, manifest)
    )

    environment = valid_environment()
    manifest["polcert_release_tag"] = "unknown"
    assert "invalid provenance field: polcert_release_tag" in (
        check_build_provenance(environment, manifest)
    )

    environment["POLCERT_REQUIRE_PROVENANCE"] = "0"
    assert check_build_provenance(environment, None) == []
    print("[release-provenance-unit] PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
