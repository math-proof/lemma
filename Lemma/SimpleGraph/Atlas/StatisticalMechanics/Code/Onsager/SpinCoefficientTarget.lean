import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SpinCoefficientTarget
open StatMech StatMech.Onsager


/--
[ons_KWmatPhase_det_eq_spinDetX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientTarget.lean)
-/
@[path]
private lemma ons_KWmatPhase_det_eq_spinDetX_eq
  {L : ℕ}
  [NeZero L]
  [Fact (1 < L)]
  {x : ℝ}
  {a b : Fin 2} :
-- imply
  (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det = (ons_spinDetX L x a b : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_det_eq_spinDetX L x a b

/--
[ons_spinKacWardAt_iff_coefficientIdentity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientTarget.lean)
-/
@[path]
private lemma ons_spinKacWardAt_iff_coefficientIdentity_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  ons_spinKacWardAt L x ↔ ons_spinCoefficientIdentity L x := by
-- proof
  apply StatMech.Onsager.ons_spinKacWardAt_iff_coefficientIdentity L x


-- created on 2026-10-23
