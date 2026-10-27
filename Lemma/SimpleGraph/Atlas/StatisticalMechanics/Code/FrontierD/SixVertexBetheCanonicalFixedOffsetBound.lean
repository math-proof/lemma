import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffsetBound
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalEvenOffsetUniformBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetBound.lean)
-/
@[path]
private lemma sixVertexCanonicalEvenOffsetUniformBound_nonneg_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 <= sixVertexCanonicalEvenOffsetUniformBound c hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalEvenOffsetUniformBound_nonneg hc s

/--
[sixVertexCanonicalOddOffsetUniformBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetBound.lean)
-/
@[path]
private lemma sixVertexCanonicalOddOffsetUniformBound_nonneg_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 <= sixVertexCanonicalOddOffsetUniformBound c hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddOffsetUniformBound_nonneg hc s

/--
[eventually_abs_sixVertexCanonicalEvenChargeOffset_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetBound.lean)
-/
@[path]
private lemma eventually_abs_sixVertexCanonicalEvenChargeOffset_le_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, forall j, := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sixVertexCanonicalEvenChargeOffset_le hc s

/--
[eventually_abs_sixVertexCanonicalOddChargeOffset_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetBound.lean)
-/
@[path]
private lemma eventually_abs_sixVertexCanonicalOddChargeOffset_le_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, forall j, := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sixVertexCanonicalOddChargeOffset_le hc s


-- created on 2026-10-23
