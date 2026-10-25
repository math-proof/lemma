import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSelectedSeamCapacity
open Finset StatMech StatMech.FrontierA


/--
[isingSurfaceTension_certificate_of_selectedSeamCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSelectedSeamCapacity.lean)
-/
@[path]
private lemma isingSurfaceTension_certificate_of_selectedSeamCapacity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {n : Nat}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 < beta)
  (hJ : forall e, 0 <= J e)
  (hhf : forall x, 0 <= hf x)
  (hr : 0 <= r)
  (hcapacity : forall q, LPReplicaAggregateSelectedSeamCapacity G sites hsite q)
  (hn : 0 < n)
  (hcritical : rectangularIsingSurfaceTension (StatMech.Ising.betaC 3) = 0) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r ((∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0) ∧ (2 * magnetization 3 beta ^ 2 * (((2 * n + 1 : Nat) : Real) ^ 2) <= fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 - fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) beta 0) ∧ (0 < rectangularIsingSurfaceTension beta <-> StatMech.Ising.betaC 3 < beta) := by
-- proof
  apply StatMech.FrontierA.isingSurfaceTension_certificate_of_selectedSeamCapacity G sites hsite beta J hf r hbeta hJ hhf hr hcapacity n hn hcritical

/--
[isingSurfaceTension_certificate_of_highRankAggregateInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSelectedSeamCapacity.lean)
-/
@[path]
private lemma isingSurfaceTension_certificate_of_highRankAggregateInjection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {n : Nat}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 < beta)
  (hJ : forall e, 0 <= J e)
  (hhf : forall x, 0 <= hf x)
  (hr : 0 <= r)
  (hhigh : forall q, 5 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q) -> LPReplicaAggregateDecoratedInjection G sites q)
  (hmean : forall m, OddPrismUnequalBridgeSymmetricMeanOrder (StatMech.Ising.betaC 3) m)
  (hn : 0 < n) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r ((∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0) ∧ (2 * magnetization 3 beta ^ 2 * (((2 * n + 1 : Nat) : Real) ^ 2) <= fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 - fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) beta 0) ∧ (0 < rectangularIsingSurfaceTension beta <-> StatMech.Ising.betaC 3 < beta) := by
-- proof
  apply StatMech.FrontierA.isingSurfaceTension_certificate_of_highRankAggregateInjection G sites hsite beta J hf r hbeta hJ hhf hr hhigh hmean n hn


-- created on 2026-10-23
