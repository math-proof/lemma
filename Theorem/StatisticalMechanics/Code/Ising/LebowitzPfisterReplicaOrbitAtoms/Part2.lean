/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitWeight.Part2
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem card_lpReplicaOrbitAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOrbitAtom G sites A B q) =
      ∑ x : LPReplicaOrbitConfiguration G sites A B q,
        lpReplicaOrbitConfigurationMultiplicity G sites A B q x := by
  classical
  unfold LPReplicaOrbitAtom
  change Fintype.card
      (Σ x : LPReplicaOrbitConfiguration G sites A B q,
        Fin (lpReplicaOrbitConfigurationMultiplicity G sites A B q x)) = _
  calc
    _ = ∑ x : LPReplicaOrbitConfiguration G sites A B q,
        Fintype.card
          (Fin (lpReplicaOrbitConfigurationMultiplicity G sites A B q x)) :=
      Fintype.card_sigma
    _ = _ := by simp


theorem lpReplicaProfileOrbitMass_eq_card_atoms_mul_base
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaProfileOrbitMass G sites beta J hf r A B q =
      (Fintype.card (LPReplicaOrbitAtom G sites A B q) : Real) *
        lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
  classical
  rw [lpReplicaProfileOrbitMass_eq_sum_configurationWeight]
  simp_rw [lpReplicaOrbitConfigurationWeight_eq_multiplicity_mul_base]
  rw [<- Finset.sum_mul]
  rw [<- Nat.cast_sum]
  rw [<- card_lpReplicaOrbitAtom G sites A B q]


theorem lpReplicaProfileOrbitBaseWeight_nonneg
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    0 <= lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
  classical
  unfold lpReplicaProfileOrbitBaseWeight
  apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro e _
  · exact div_nonneg
      (pow_nonneg (mul_nonneg hbeta
        (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr e.1)) _)
      (by positivity)
  · exact div_nonneg
      (pow_nonneg (mul_nonneg hbeta
        (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr e.1)) _)
      (by positivity)


theorem lpReplicaProfileOrbitMass_le_add_of_card_atoms
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B C D E F : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitAtom G sites A B q) <=
      Fintype.card (LPReplicaOrbitAtom G sites C D q) +
        Fintype.card (LPReplicaOrbitAtom G sites E F q)) :
    lpReplicaProfileOrbitMass G sites beta J hf r A B q <=
      lpReplicaProfileOrbitMass G sites beta J hf r C D q +
        lpReplicaProfileOrbitMass G sites beta J hf r E F q := by
  rw [lpReplicaProfileOrbitMass_eq_card_atoms_mul_base,
    lpReplicaProfileOrbitMass_eq_card_atoms_mul_base,
    lpReplicaProfileOrbitMass_eq_card_atoms_mul_base]
  have hcardReal :
      (Fintype.card (LPReplicaOrbitAtom G sites A B q) : Real) <=
        Fintype.card (LPReplicaOrbitAtom G sites C D q) +
          Fintype.card (LPReplicaOrbitAtom G sites E F q) := by
    exact_mod_cast hcard
  have hbase := lpReplicaProfileOrbitBaseWeight_nonneg
    G sites beta J hf r hbeta hJ hhf hr q
  nlinarith only [mul_le_mul_of_nonneg_right hcardReal hbase]


end
end StatMech.Ising
