import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.EdgeMarginalInfinite
open MeasureTheory StatMech StatMech.FK


/--
[emi_mass_eq_of_edgeMarg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginalInfinite.lean)
-/
@[path]
private lemma emi_mass_eq_of_edgeMarg_eq_eq
  [Fintype E]
  [DecidableEq E]
  {P : ConfigSpace E × ConfigSpace E → ℝ}
  {μ ν : ConfigSpace E → ℝ}
-- given
  (hP : IsMonotoneCouplingFun P μ ν)
  (hmarg : ∀ e, edgeMargProb μ e = edgeMargProb ν e) :
-- imply
  μ = ν := by
-- proof
  apply StatMech.FK.emi_mass_eq_of_edgeMarg_eq hP hmarg

/--
[infiniteMeasure_eq_of_edgeMarg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginalInfinite.lean)
-/
@[path]
private lemma infiniteMeasure_eq_of_edgeMarg_eq_eq
  [DecidableEq E]
  {μ ν : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν]
-- given
  (hdom : μ ≼ ν)
  (hmarg : ∀ e : E, μ.real {ω | ω e = true} = ν.real {ω | ω e = true}) :
-- imply
  μ = ν := by
-- proof
  apply StatMech.FK.infiniteMeasure_eq_of_edgeMarg_eq μ ν hdom hmarg


-- created on 2026-10-23
