import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms
open Finset StatMech StatMech.Ising


/--
[lpReplicaOrbitConfigurationWeight_eq_multiplicity_mul_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAtoms.lean)
-/
@[path]
private lemma lpReplicaOrbitConfigurationWeight_eq_multiplicity_mul_base_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {x : LPReplicaOrbitConfiguration G sites A B q}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitConfigurationWeight G sites beta J hf r A B q x = (lpReplicaOrbitConfigurationMultiplicity G sites A B q x : Real) * lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitConfigurationWeight_eq_multiplicity_mul_base G sites beta J hf r A B q x

/--
[card_lpReplicaOrbitAtom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAtoms.lean)
-/
@[path]
private lemma card_lpReplicaOrbitAtom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOrbitAtom G sites A B q) = ∑ x : LPReplicaOrbitConfiguration G sites A B q, lpReplicaOrbitConfigurationMultiplicity G sites A B q x := by
-- proof
  apply StatMech.Ising.card_lpReplicaOrbitAtom G sites A B q

/--
[lpReplicaProfileOrbitMass_eq_card_atoms_mul_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAtoms.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitMass_eq_card_atoms_mul_base_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaProfileOrbitMass G sites beta J hf r A B q = (Fintype.card (LPReplicaOrbitAtom G sites A B q) : Real) * lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitMass_eq_card_atoms_mul_base G sites beta J hf r A B q

/--
[lpReplicaProfileOrbitBaseWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAtoms.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitBaseWeight_nonneg_eq
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
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  0 <= lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitBaseWeight_nonneg G sites beta J hf r hbeta hJ hhf hr q

/--
[lpReplicaProfileOrbitMass_le_add_of_card_atoms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAtoms.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitMass_le_add_of_card_atoms_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B C D E F : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitAtom G sites A B q) <= Fintype.card (LPReplicaOrbitAtom G sites C D q) + Fintype.card (LPReplicaOrbitAtom G sites E F q)) :
-- imply
  lpReplicaProfileOrbitMass G sites beta J hf r A B q <= lpReplicaProfileOrbitMass G sites beta J hf r C D q + lpReplicaProfileOrbitMass G sites beta J hf r E F q := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitMass_le_add_of_card_atoms G sites beta J hf r hbeta hJ hhf hr A B C D E F q hcard

/--
[lpReplicaAggregateProfileOrbitInequality_of_atomCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAtoms.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_atomCard_eq
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
  (hcard : ∀ q i j, i ≠ j -> LPReplicaOffdiagOrbitAtomCardInequality G sites i j q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_atomCard G sites beta J hf r hbeta hJ hhf hr hcard


-- created on 2026-10-23
