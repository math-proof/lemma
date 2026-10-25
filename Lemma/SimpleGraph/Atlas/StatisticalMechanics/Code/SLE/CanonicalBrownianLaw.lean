import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.CanonicalBrownianLaw
open MeasureTheory ProbabilityTheory StatMech StatMech.SLE


/--
[brownianContinuousModification_processLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianLaw.lean)
-/
@[path]
private lemma brownianContinuousModification_processLaw_eq :
-- imply
  brownianProductLaw.map (fun omega t => brownianContinuousModification t omega) = brownianProductLaw := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_processLaw

/--
[brownianContinuousModification_sleDriving_processLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianLaw.lean)
-/
@[path]
private lemma brownianContinuousModification_sleDriving_processLaw_eq
  {kappa : Real} :
-- imply
  brownianProductLaw.map (fun omega => sleDriving kappa brownianContinuousModification omega) = brownianProductLaw.map (fun b : Real -> Real => fun t => Real.sqrt kappa * b t) := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_sleDriving_processLaw kappa


-- created on 2026-10-23
