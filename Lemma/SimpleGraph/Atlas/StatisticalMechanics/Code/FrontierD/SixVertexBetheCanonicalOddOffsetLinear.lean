import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddOffsetLinear.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalOddOffsetLinearBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddOffsetLinear.lean)
-/
@[path]
private lemma sixVertexCanonicalOddOffsetLinearBound_nonneg_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 <= sixVertexCanonicalOddOffsetLinearBound c hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddOffsetLinearBound_nonneg hc s

/--
[sixVertexCanonicalOddOffsetRemainderBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddOffsetLinear.lean)
-/
@[path]
private lemma sixVertexCanonicalOddOffsetRemainderBound_nonneg_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 <= sixVertexCanonicalOddOffsetRemainderBound c hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddOffsetRemainderBound_nonneg hc s

/--
[eventually_abs_sixVertexCanonicalOddChargeOffset_le_linear_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddOffsetLinear.lean)
-/
@[path]
private lemma eventually_abs_sixVertexCanonicalOddChargeOffset_le_linear_add_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, forall j, := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sixVertexCanonicalOddChargeOffset_le_linear_add hc s


-- created on 2026-10-23
