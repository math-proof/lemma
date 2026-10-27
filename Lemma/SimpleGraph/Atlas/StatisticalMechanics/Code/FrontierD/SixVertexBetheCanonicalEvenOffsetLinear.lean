import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalEvenOffsetLinear.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalEvenOffsetLinearBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalEvenOffsetLinear.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenOffsetLinearBound_nonneg_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 <= sixVertexCanonicalEvenOffsetLinearBound c hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenOffsetLinearBound_nonneg hc s

/--
[eventually_abs_sixVertexCanonicalEvenChargeOffset_le_mul_abs_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalEvenOffsetLinear.lean)
-/
@[path]
private lemma eventually_abs_sixVertexCanonicalEvenChargeOffset_le_mul_abs_aligned_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, forall j, := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sixVertexCanonicalEvenChargeOffset_le_mul_abs_aligned hc s


-- created on 2026-10-23
