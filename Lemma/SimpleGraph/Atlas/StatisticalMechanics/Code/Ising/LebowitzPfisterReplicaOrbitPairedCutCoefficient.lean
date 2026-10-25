import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutCoefficient
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoPairedCuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutCoefficient.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoPairedCuts_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcuts : forall (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) (z : LPReplicaOffdiagDecoratedSource G sites i j q), LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable G sites i j q hcard z) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoPairedCuts G sites hsite hij q hcuts

/--
[lpReplicaAggregateProfileOrbitInequality_of_canonicalLastTwoPairedCuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutCoefficient.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_canonicalLastTwoPairedCuts_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hcuts : ∀ q i j, i ≠ j -> ∀ (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) (z : LPReplicaOffdiagDecoratedSource G sites i j q), LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable G sites i j q hcard z) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_canonicalLastTwoPairedCuts G sites hsite beta J hf r hbeta hJ hhf hr hcuts

/--
[lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_canonicalLastTwoPairedCuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutCoefficient.lean)
-/
@[path]
private lemma lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_canonicalLastTwoPairedCuts_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hcuts : ∀ q i j, i ≠ j -> ∀ (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) (z : LPReplicaOffdiagDecoratedSource G sites i j q), LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable G sites i j q hcard z) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r (∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_canonicalLastTwoPairedCuts G sites hsite beta J hf r hbeta hJ hhf hr hcuts


-- created on 2026-10-23
