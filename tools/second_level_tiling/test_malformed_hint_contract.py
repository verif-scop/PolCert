import unittest

from check_rejected_tiling_route import (
    hinted_malformed_rejection_stage, final_affine_rejection_stage, REJECTED_ROUTE, BAND_ROUTE,
)


PREFLIGHT = (
    "[parallel-validation] proposal=actual reason=instance-space-mismatch\n"
    "[parallel-validation] proposal=actual reason=no-compatible-candidate\n"
    "[parallel-validation] status=rejected source=pluto-hint reason=no-certifiable-dimension\n"
)
AFFINE = (
    "[parallel-validation] scope=phase reason=affine-rejected\n"
    "[parallel-validation] proposal=actual coordinate=0 accepted=false nontrivial=false\n"
    "[parallel-validation] status=rejected source=pluto-hint reason=no-certifiable-dimension\n"
)


class MalformedHintBoundary(unittest.TestCase):
    def test_formal_tiling_rejection(self):
        self.assertEqual(hinted_malformed_rejection_stage("parallel", REJECTED_ROUTE), "tiling")

    def test_explicit_strict_preflight(self):
        self.assertEqual(hinted_malformed_rejection_stage("parallel-strict", PREFLIGHT), "parallel-preflight")

    def test_unexplained_missing_hint_is_not_enough(self):
        self.assertIsNone(hinted_malformed_rejection_stage("parallel-strict", PREFLIGHT.splitlines()[-1]))

    def test_non_strict_cannot_use_preflight_exception(self):
        self.assertIsNone(hinted_malformed_rejection_stage("parallel", PREFLIGHT))

    def test_missing_instance_mismatch_is_not_preflight(self):
        unexplained = PREFLIGHT.replace("[parallel-validation] proposal=actual reason=instance-space-mismatch\n", "")
        self.assertIsNone(hinted_malformed_rejection_stage("parallel-strict", unexplained))
        self.assertEqual(hinted_malformed_rejection_stage(
            "parallel-strict", unexplained, reader_rejection_confirmed=True), "parallel-reader")

    def test_successful_tiling_is_not_rejection(self):
        self.assertIsNone(hinted_malformed_rejection_stage("parallel-strict", BAND_ROUTE + "\n" + PREFLIGHT))

    def test_two_rejection_stages_are_not_unique(self):
        self.assertIsNone(hinted_malformed_rejection_stage("parallel-strict", REJECTED_ROUTE + "\n" + PREFLIGHT))

    def test_normal_final_affine(self):
        self.assertEqual(final_affine_rejection_stage("sequential", BAND_ROUTE), "final-affine")

    def test_strict_candidate_affine(self):
        self.assertEqual(final_affine_rejection_stage("parallel-hint-strict", AFFINE), "parallel-candidate-affine")

    def test_preflight_is_not_final_affine(self):
        self.assertIsNone(final_affine_rejection_stage("parallel-hint-strict", PREFLIGHT))

    def test_non_strict_may_not_drop_the_tiling_route(self):
        self.assertIsNone(final_affine_rejection_stage("sequential", AFFINE))

    def test_missing_candidate_failure(self):
        self.assertIsNone(final_affine_rejection_stage("parallel-hint-strict", AFFINE.replace("accepted=false", "accepted=true")))


if __name__ == "__main__":
    unittest.main()
