import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
open StatMech StatMech.FrontierA


/--
[kw_four_signs_have_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFourSignMajority.lean)
-/
@[path]
private lemma kw_four_signs_have_ear_eq
  {s0 s1 s2 s3 : Real}
-- given
  (h0 : s0 ≠ 0)
  (h1 : s1 ≠ 0)
  (h2 : s2 ≠ 0)
  (h3 : s3 ≠ 0)
  (hNo02 : ¬(s0 * s3 < 0 ∧ s1 * s2 < 0))
  (hNo13 : ¬(s1 * s0 < 0 ∧ s2 * s3 < 0)) :
-- imply
  (((0 < s3 ∧ 0 < s0 ∧ 0 < s2) ∨ (s3 < 0 ∧ s0 < 0 ∧ s2 < 0)) ∨ ((0 < s0 ∧ 0 < s1 ∧ 0 < s3) ∨ (s0 < 0 ∧ s1 < 0 ∧ s3 < 0)) ∨ ((0 < s1 ∧ 0 < s2 ∧ 0 < s0) ∨ (s1 < 0 ∧ s2 < 0 ∧ s0 < 0)) ∨ ((0 < s2 ∧ 0 < s3 ∧ 0 < s1) ∨ (s2 < 0 ∧ s3 < 0 ∧ s1 < 0))) := by
-- proof
  apply StatMech.FrontierA.kw_four_signs_have_ear h0 h1 h2 h3 hNo02 hNo13


-- created on 2026-10-23
