import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms
open Finset StatMech StatMech.Ising


/--
[lpReplicaCollisionSplitMultiplicity_eq_edgeProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean)
-/
@[path]
private lemma lpReplicaCollisionSplitMultiplicity_eq_edgeProduct_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCollisionSplitMultiplicity G sites m K = ∏ e : (lpReplicaCurrentGraph G sites).edgeFinset, Nat.choose (m e) (K e) := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionSplitMultiplicity_eq_edgeProduct G sites m K

/--
[card_lpReplicaCollisionSplitLabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean)
-/
@[path]
private lemma card_lpReplicaCollisionSplitLabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaCollisionSplitLabel G sites m K) = lpReplicaCollisionSplitMultiplicity G sites m K := by
-- proof
  apply StatMech.Ising.card_lpReplicaCollisionSplitLabel G sites m K

/--
[card_lpReplicaProfileOrbitLabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean)
-/
@[path]
private lemma card_lpReplicaProfileOrbitLabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaProfileOrbitLabel G sites q m) = lpReplicaProfileOrbitMultiplicity G sites q m := by
-- proof
  apply StatMech.Ising.card_lpReplicaProfileOrbitLabel G sites q m

/--
[card_lpReplicaDecoratedOrbitAtom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean)
-/
@[path]
private lemma card_lpReplicaDecoratedOrbitAtom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaDecoratedOrbitAtom G sites A B q) = Fintype.card (LPReplicaOrbitAtom G sites A B q) := by
-- proof
  apply StatMech.Ising.card_lpReplicaDecoratedOrbitAtom G sites A B q

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hinj : LPReplicaOffdiagDecoratedOrbitInjection G sites i j q) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection G sites i j q hinj

/--
[lpReplicaAggregateProfileOrbitInequality_of_decoratedInjections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_decoratedInjections_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hinj : ∀ q i j, i ≠ j -> LPReplicaOffdiagDecoratedOrbitInjection G sites i j q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_decoratedInjections G sites beta J hf r hbeta hJ hhf hr hinj


-- created on 2026-10-23
