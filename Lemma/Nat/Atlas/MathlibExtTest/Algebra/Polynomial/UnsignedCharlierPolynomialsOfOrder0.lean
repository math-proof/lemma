import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Algebra.Polynomial.UnsignedCharlierPolynomialsOfOrder0


namespace MetaMathlibExt

/--
[unsignedCharlierOrder0_nat_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/UnsignedCharlierPolynomialsOfOrder0.lean)
-/
@[path]
lemma unsignedCharlierOrder0_nat_zero
-- imply
  unsignedCharlierOrder0 ℕ 0 = 1 := by
-- proof
  simp [unsignedCharlierOrder0, ascPochhammer_zero]
  try ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unsignedCharlierOrder0_nat_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/UnsignedCharlierPolynomialsOfOrder0.lean)
-/
@[path]
lemma unsignedCharlierOrder0_nat_one
-- imply
  unsignedCharlierOrder0 ℕ 1 = 1 + Polynomial.X := by
-- proof
  simp [unsignedCharlierOrder0, ascPochhammer_zero, ascPochhammer_succ_right, Finset.sum_range_succ]
  try ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unsignedCharlierOrder0_nat_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/UnsignedCharlierPolynomialsOfOrder0.lean)
-/
@[path]
lemma unsignedCharlierOrder0_nat_two
-- imply
  unsignedCharlierOrder0 ℕ 2 = 1 + 3 * Polynomial.X + Polynomial.X ^ 2 := by
-- proof
  simp [unsignedCharlierOrder0, ascPochhammer_zero, ascPochhammer_succ_right, Finset.sum_range_succ]
  try ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unsignedCharlierOrder0_nat_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/UnsignedCharlierPolynomialsOfOrder0.lean)
-/
@[path]
lemma unsignedCharlierOrder0_nat_three
-- imply
  unsignedCharlierOrder0 ℕ 3 = 1 + 8 * Polynomial.X + 6 * Polynomial.X ^ 2 + Polynomial.X ^ 3 := by
-- proof
  simp [unsignedCharlierOrder0, ascPochhammer_zero, ascPochhammer_succ_right, Finset.sum_range_succ]
  try ring

end MetaMathlibExt


-- created on 2026-10-23
