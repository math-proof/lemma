import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingCriticalBridgeEndpoint
open Filter Topology StatMech StatMech.FrontierA


/--
[oddPrismCriticalLowerHalfBridgeMeanDensity_eq_spinSquareAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBridgeEndpoint.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfBridgeMeanDensity_eq_spinSquareAverage_eq
  {n : Nat} :
-- imply
  oddPrismCriticalLowerHalfBridgeMeanDensity n = oddPrismCriticalLowerHalfSpinSquareAverage n := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfBridgeMeanDensity_eq_spinSquareAverage n

/--
[oddPrismCriticalLowerHalfBridgeMeanDensity_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBridgeEndpoint.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfBridgeMeanDensity_tendsto_zero_eq :
-- imply
  Tendsto oddPrismCriticalLowerHalfBridgeMeanDensity atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfBridgeMeanDensity_tendsto_zero

/--
[oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBridgeEndpoint.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity_eq_eq
  {n : Nat} :
-- imply
  oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity n = 2 * oddPrismCriticalLowerHalfBridgeMeanDensity n := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity_eq n

/--
[oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBridgeEndpoint.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity_tendsto_zero_eq :
-- imply
  Tendsto oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfBridgeInitialDerivativeDensity_tendsto_zero

/--
[oddPrismCriticalLowerHalfBridge_eventually_le_of_variance_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBridgeEndpoint.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfBridge_eventually_le_of_variance_order_eq
  {eps : Real}
-- given
  (hvar : forall n, letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _ forall t, 0 <= t -> replicaBridgeVariance (oddPrismLowerHalfGraph n) (fun _ => Ising.betaC 3) (fun v => Ising.betaC 3 * oddPrismPlusField n v.1) (oddPrismLowerHalfBridgeSites n) t <= replicaBridgeVariance (oddPrismLowerHalfGraph n) (fun _ => Ising.betaC 3) (fun v => Ising.betaC 3 * oddPrismPlusField n v.1) (oddPrismLowerHalfBridgeSites n) (-t))
  (heps : 0 < eps) :
-- imply
  Filter.Eventually (fun n => oddPrismLowerHalfBridgeFreeEnergy (Ising.betaC 3) n / (((2 * n + 1 : Nat) : Real) ^ 2) <= eps) atTop := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfBridge_eventually_le_of_variance_order hvar eps heps


-- created on 2026-10-23
