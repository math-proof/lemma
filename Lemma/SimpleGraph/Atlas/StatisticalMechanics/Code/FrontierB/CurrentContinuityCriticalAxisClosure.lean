import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentContinuityCriticalAxisClosure
open MeasureTheory StatMech StatMech.FrontierB


/--
[isingCritical_magnetization_zero_and_gibbs_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityCriticalAxisClosure.lean)
-/
@[path]
private lemma isingCritical_magnetization_zero_and_gibbs_unique_eq
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  magnetization d (IsingFK.betaC (magnetization d)) = 0 ∧ ∀ (mu : Measure (ConfigSpace (Lattice.Site d))) [IsProbabilityMeasure mu], IsDLRState d (IsingFK.betaC (magnetization d)) 0 mu → mu = (minusState d (IsingFK.betaC (magnetization d)) 0 : Measure (ConfigSpace (Lattice.Site d))) := by
-- proof
  apply StatMech.FrontierB.isingCritical_magnetization_zero_and_gibbs_unique hd


-- created on 2026-10-23
