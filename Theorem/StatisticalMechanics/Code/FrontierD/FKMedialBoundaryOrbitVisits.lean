/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitVisits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitReachability
import Def.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitVisits
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


theorem perm_pow_fin_add {α : Type*}
    (σ : Perm α) [NeZero (orderOf σ)]
    (i k : Fin (orderOf σ)) :
    σ ^ ((i + k : Fin (orderOf σ)) : Nat) =
      σ ^ ((i : Nat) + (k : Nat)) := by
  rw [← pow_mod_orderOf σ ((i : Nat) + (k : Nat))]
  congr


theorem permOrbitVisitCount_eq_of_sameCycle
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (d a b : α) (hab : σ.SameCycle a b) :
    permOrbitVisitCount σ d a = permOrbitVisitCount σ d b := by
  classical
  letI : NeZero (orderOf σ) := ⟨(orderOf_pos σ).ne'⟩
  obtain ⟨k, hklt, hk⟩ := hab.exists_pow_eq'
  let kfin : Fin (orderOf σ) := ⟨k, hklt⟩
  unfold permOrbitVisitCount
  rw [← Equiv.sum_comp (Equiv.addRight kfin)
    (fun i : Fin (orderOf σ) =>
      if (σ ^ (i : Nat)) d = b then 1 else 0)]
  apply Finset.sum_congr rfl
  intro i hi
  change (if (σ ^ (i : Nat)) d = a then 1 else 0) =
    if (σ ^ ((i + kfin : Fin (orderOf σ)) : Nat)) d = b then 1 else 0
  rw [perm_pow_fin_add]
  rw [Nat.add_comm (i : Nat) (kfin : Nat)]
  simp only [pow_add, Perm.mul_apply]
  rw [← show (σ ^ (kfin : Nat)) a = b by exact hk]
  simp only [Equiv.apply_eq_iff_eq]


theorem permOrbitVisitCount_pos_iff_sameCycle
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (d e : α) :
    0 < permOrbitVisitCount σ d e ↔ σ.SameCycle d e := by
  classical
  unfold permOrbitVisitCount
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨i, -, hi⟩
    have heq : (σ ^ (i : Nat)) d = e := by
      by_contra hne
      simp [hne] at hi
    refine ⟨(i : Nat), ?_⟩
    simpa only [zpow_natCast] using heq
  · intro hcycle
    obtain ⟨i, hi⟩ := hcycle.exists_fin_pow_eq
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simp [hi]


theorem permOrbitVisitCount_eq_zero_iff_not_sameCycle
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (d e : α) :
    permOrbitVisitCount σ d e = 0 ↔ ¬ σ.SameCycle d e := by
  rw [← permOrbitVisitCount_pos_iff_sameCycle]
  omega


end
end StatMech.FrontierD
