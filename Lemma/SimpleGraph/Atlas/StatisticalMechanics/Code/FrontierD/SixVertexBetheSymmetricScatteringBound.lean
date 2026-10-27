import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricScatteringBound.Part3
open StatMech StatMech.FrontierD


/--
[hasDerivAt_sixVertexSymmetricScatteringPhase_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexSymmetricScatteringPhase_right_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  HasDerivAt (sixVertexSymmetricScatteringPhase c x) (sixVertexSymmetricScatteringDerivative c x y) y := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexSymmetricScatteringPhase_right hc x y

/--
[continuous_sixVertexSymmetricScatteringDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean)
-/
@[path]
private lemma continuous_sixVertexSymmetricScatteringDerivative_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  Continuous (sixVertexSymmetricScatteringDerivative c x) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexSymmetricScatteringDerivative hc x

/--
[lipschitzWith_sixVertexSymmetricScatteringDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexSymmetricScatteringDerivative_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  LipschitzWith (sixVertexSymmetricScatteringLipschitzConstant c) (sixVertexSymmetricScatteringDerivative c x) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexSymmetricScatteringDerivative hc x

/--
[abs_sixVertexSymmetricScatteringDerivative_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean)
-/
@[path]
private lemma abs_sixVertexSymmetricScatteringDerivative_le_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexSymmetricScatteringDerivative c x y| ≤ 2 * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexSymmetricScatteringDerivative_le hc x y

/--
[intervalIntegral_sixVertexSymmetricScatteringDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexSymmetricScatteringDerivative_eq
  {c : Real}
  {x a b : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∫ y in a..b, sixVertexSymmetricScatteringDerivative c x y = sixVertexSymmetricScatteringPhase c x b - sixVertexSymmetricScatteringPhase c x a := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexSymmetricScatteringDerivative hc x a b

/--
[sixVertexSymmetricScatteringBoundaryIncrement_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean)
-/
@[path]
private lemma sixVertexSymmetricScatteringBoundaryIncrement_eq_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hx : x ∈ Set.Icc (-Real.pi) 0) :
-- imply
  sixVertexSymmetricScatteringBoundaryIncrement c x = 4 * Real.arctan ((-Real.sin x) / (2 * sixVertexAnisotropyMagnitude c * (Real.cos x + sixVertexAnisotropyMagnitude c))) := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricScatteringBoundaryIncrement_eq hc hx

/--
[sixVertexSymmetricScatteringBoundaryBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean)
-/
@[path]
private lemma sixVertexSymmetricScatteringBoundaryBound_nonneg_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 ≤ sixVertexSymmetricScatteringBoundaryBound c := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricScatteringBoundaryBound_nonneg hc

/--
[sixVertexSymmetricScatteringBoundaryBound_lt_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean)
-/
@[path]
private lemma sixVertexSymmetricScatteringBoundaryBound_lt_two_pi_eq
  {c : Real} :
-- imply
  sixVertexSymmetricScatteringBoundaryBound c < 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricScatteringBoundaryBound_lt_two_pi

/--
[sixVertexSymmetricScatteringBoundaryIncrement_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean)
-/
@[path]
private lemma sixVertexSymmetricScatteringBoundaryIncrement_bounds_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hx : x ∈ Set.Icc (-Real.pi) 0) :
-- imply
  0 ≤ sixVertexSymmetricScatteringBoundaryIncrement c x ∧ sixVertexSymmetricScatteringBoundaryIncrement c x ≤ sixVertexSymmetricScatteringBoundaryBound c := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricScatteringBoundaryIncrement_bounds hc hx


-- created on 2026-10-23
