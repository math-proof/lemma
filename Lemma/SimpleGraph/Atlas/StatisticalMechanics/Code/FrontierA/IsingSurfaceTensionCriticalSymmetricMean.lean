import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalSymmetricMean
open Filter Set Topology StatMech StatMech.FrontierA


/--
[unequalReplicaBridgeFreeEnergy_le_of_symmetric_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalSymmetricMean.lean)
-/
@[path]
private lemma unequalReplicaBridgeFreeEnergy_le_of_symmetric_mean_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
  {J : Real}
  {r : Real}
-- given
  (hf : V -> Real)
  (hg : W -> Real)
  (hr : 0 <= r)
  (hmean : forall t, 0 <= t -> t <= r -> unequalReplicaBridgeMean G H K J hf hg t + unequalReplicaBridgeMean G H K J hf hg (-t) <= 2 * unequalReplicaBridgeMean G H K J hf hg 0) :
-- imply
  unequalReplicaBridgeFreeEnergy G H K J hf hg r <= 2 * r * unequalReplicaBridgeMean G H K J hf hg 0 := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeFreeEnergy_le_of_symmetric_mean G H K J hf hg r hr hmean

/--
[oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalSymmetricMean.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder_eq
  {beta : Real}
  {n : Nat}
-- given
  (hvar : OddPrismUnequalBridgeVarianceOrder beta n) :
-- imply
  OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder hvar

/--
[oddPrismUnequalBridgeFreeEnergy_le_of_symmetricMeanOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalSymmetricMean.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeFreeEnergy_le_of_symmetricMeanOrder_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hmean : OddPrismUnequalBridgeSymmetricMeanOrder beta n) :
-- imply
  oddPrismUnequalBridgeFreeEnergy beta n <= 2 * beta * unequalReplicaBridgeMean (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) beta (fun v => beta * oddPrismPlusField n v.1) (fun v => beta * oddPrismPlusField n v.1) 0 := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeFreeEnergy_le_of_symmetricMeanOrder beta hbeta n hmean

/--
[standardCubicInterfaceDensity_critical_le_unequalMeanDensity_of_symmetricMeanOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalSymmetricMean.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_critical_le_unequalMeanDensity_of_symmetricMeanOrder_eq
  {n : Nat}
-- given
  (hn : 0 < n)
  (hmean : OddPrismUnequalBridgeSymmetricMeanOrder (Ising.betaC 3) n) :
-- imply
  standardCubicInterfaceDensity (Ising.betaC 3) n <= 2 * Ising.betaC 3 * oddPrismCriticalUnequalBridgeMeanDensity n := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_critical_le_unequalMeanDensity_of_symmetricMeanOrder n hn hmean

/--
[standardCubicInterfaceDensity_critical_tendsto_zero_of_symmetricMeanOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalSymmetricMean.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_critical_tendsto_zero_of_symmetricMeanOrder_eq
-- given
  (hmean : forall n, OddPrismUnequalBridgeSymmetricMeanOrder (Ising.betaC 3) n) :
-- imply
  Tendsto (standardCubicInterfaceDensity (Ising.betaC 3)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_critical_tendsto_zero_of_symmetricMeanOrder hmean

/--
[rectangularIsingSurfaceTension_critical_eq_zero_of_symmetricMeanOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalSymmetricMean.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_critical_eq_zero_of_symmetricMeanOrder_eq
-- given
  (hprism : HasPrismCubicalSurfaceComparison (Ising.betaC 3))
  (hmean : forall n, OddPrismUnequalBridgeSymmetricMeanOrder (Ising.betaC 3) n) :
-- imply
  rectangularIsingSurfaceTension (Ising.betaC 3) = 0 := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_critical_eq_zero_of_symmetricMeanOrder hprism hmean


-- created on 2026-10-23
