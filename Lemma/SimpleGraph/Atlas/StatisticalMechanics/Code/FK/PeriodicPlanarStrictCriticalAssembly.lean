import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictCriticalAssembly
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[dualCritical_relation_of_exponentialDecay_strictNoCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictCriticalAssembly.lean)
-/
@[path]
private lemma dualCritical_relation_of_exponentialDecay_strictNoCoexistence_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {q : Real}
-- given
  (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
  (hq : 1 ≤ q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hstrict : StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_exponentialDecay_strictNoCoexistence D H hpc hpcDual hq hdecay hstrict

/--
[dualCritical_relation_of_bidirectionalExponentialDecay_strictNoCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarStrictCriticalAssembly.lean)
-/
@[path]
private lemma dualCritical_relation_of_bidirectionalExponentialDecay_strictNoCoexistence_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {Hdual : PolynomialConnectionShells D.swap}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hdecayDual : SubcriticalTwoPointExponentialDecay Pdual q (Pdual.criticalPoint q))
  (hstrict : StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_bidirectionalExponentialDecay_strictNoCoexistence D H Hdual hq hdecay hdecayDual hstrict


-- created on 2026-10-23
