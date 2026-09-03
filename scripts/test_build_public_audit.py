"""Source coverage tests; the generated Lean commands require cloud checking."""
import unittest

from public_theorem_audit import public_theorems


class PublicAuditCoverageTests(unittest.TestCase):
    def test_scopes_attributes_private_and_comments(self):
        source = """noncomputable section
namespace Outer.Inner
section Local
-- theorem fake : False := by sorry
@[simp] theorem first : True := by trivial
private theorem helper : True := by trivial
end Local
namespace Child
protected theorem second : True := by trivial
theorem _root_.Elsewhere.third : True := by trivial
end Child
end Outer.Inner
"""
        self.assertEqual(public_theorems(source),
                         ["Outer.Inner.first", "Outer.Inner.Child.second", "Elsewhere.third"])

    def test_reject_mismatched_and_unclosed_scopes(self):
        for source in ["end Wrong", "namespace A\nend B", "namespace A",
                       "section Named", "namespace A\nnamespace B\nend A"]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                public_theorems(source)

    def test_reject_duplicate_or_unsupported_declarations(self):
        for source in ["theorem a : True := by trivial\ntheorem a : True := by trivial",
                       "  theorem nested : True := by trivial"]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                public_theorems(source)


if __name__ == "__main__":
    unittest.main()
