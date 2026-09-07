"""Check that the regression collector cannot count generic fallback as direct."""

import unittest

from check_scalar_two_level_routes import accepted_direct


class DirectRouteGate(unittest.TestCase):
    def test_direct(self):
        self.assertTrue(accepted_direct(0, "== Optimized Loop ==", "[tiling-validation] route=permutable-band"))

    def test_general_is_not_direct(self):
        self.assertFalse(accepted_direct(0, "== Optimized Loop ==", "[tiling-validation] route=actual-schedule"))

    def test_missing_output(self):
        self.assertFalse(accepted_direct(0, "", "[tiling-validation] route=permutable-band"))

    def test_alarm(self):
        self.assertFalse(accepted_direct(0, "== Optimized Loop ==", "[tiling-validation] route=permutable-band\n[alarm] fail"))

    def test_multiple_routes(self):
        self.assertFalse(accepted_direct(0, "== Optimized Loop ==", "[tiling-validation] route=actual-schedule\n[tiling-validation] route=permutable-band"))


if __name__ == "__main__":
    unittest.main()
