/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3
import Def.StatisticalMechanics.Code.Onsager.SpinCharacter


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_homologyIntersection_add_right
    (h k l : Fin 2 × Fin 2) :
    ons_homologyIntersection h (k + l) =
      ons_homologyIntersection h k + ons_homologyIntersection h l := by
  rcases h with ⟨h1, h2⟩
  rcases k with ⟨k1, k2⟩
  rcases l with ⟨l1, l2⟩
  fin_cases h1 <;> fin_cases h2 <;> fin_cases k1 <;> fin_cases k2 <;>
    fin_cases l1 <;> fin_cases l2 <;> decide

theorem ons_homologyIntersection_sum_right
    {iota : Type*} (h : Fin 2 × Fin 2) (S : Finset iota)
    (f : iota → Fin 2 × Fin 2) :
    ons_homologyIntersection h (∑ i ∈ S, f i) =
      ∑ i ∈ S, ons_homologyIntersection h (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ons_homologyIntersection]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        ons_homologyIntersection_add_right, ih]

theorem ons_spinCharacter_add (a b : Fin 2) (h k : Fin 2 × Fin 2) :
    ons_spinCharacter a b (h + k) =
      ons_spinCharacter a b h * ons_spinCharacter a b k *
        (-1 : ℝ) ^ (ons_homologyIntersection h k).val := by
  rcases h with ⟨h1, h2⟩
  rcases k with ⟨k1, k2⟩
  fin_cases a <;> fin_cases b <;> fin_cases h1 <;> fin_cases h2 <;>
    fin_cases k1 <;> fin_cases k2 <;>
    norm_num [ons_spinCharacter, ons_homologyIntersection, Fin.val_add]

theorem ons_spinCharacter_add_of_intersection_zero
    (a b : Fin 2) (h k : Fin 2 × Fin 2)
    (hzero : ons_homologyIntersection h k = 0) :
    ons_spinCharacter a b (h + k) =
      ons_spinCharacter a b h * ons_spinCharacter a b k := by
  rw [ons_spinCharacter_add, hzero]
  norm_num

theorem ons_spinCharacter_sum_of_pairwise_intersection_zero
    {iota : Type*} (a b : Fin 2) (S : Finset iota)
    (f : iota → Fin 2 × Fin 2)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ons_homologyIntersection (f i) (f j) = 0) :
    ons_spinCharacter a b (∑ i ∈ S, f i) =
      ∏ i ∈ S, ons_spinCharacter a b (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [ons_spinCharacter]
  | @insert i S hi ih =>
      have hpairS : ∀ j ∈ S, ∀ k ∈ S, j ≠ k →
          ons_homologyIntersection (f j) (f k) = 0 := by
        intro j hj k hk hjk
        exact hpair j (by simp [hj]) k (by simp [hk]) hjk
      have hinter : ons_homologyIntersection (f i) (∑ j ∈ S, f j) = 0 := by
        rw [ons_homologyIntersection_sum_right]
        apply Finset.sum_eq_zero
        intro j hj
        exact hpair i (by simp) j (by simp [hj]) (by
          intro hij
          subst j
          exact hi hj)
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        ons_spinCharacter_add_of_intersection_zero a b _ _ hinter,
        ih hpairS]

end StatMech.Onsager
