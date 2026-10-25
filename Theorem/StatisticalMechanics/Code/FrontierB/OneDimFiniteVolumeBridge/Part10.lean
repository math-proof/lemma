/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part10
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma fvPathState_zero (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    fvPathState eta n tau 0 = fvLeftBoundaryState eta n := by
  unfold fvPathState fvLeftBoundaryState
  rw [glue_not_mem]
  · simp
  · rw [site1_mem_box_iff]
    omega

lemma fvPathState_right (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    fvPathState eta n tau (2 * n + 2) = fvRightBoundaryState eta n := by
  unfold fvPathState fvRightBoundaryState
  rw [show -(n : ℤ) - 1 + ((2 * n + 2 : ℕ) : ℤ) = (n : ℤ) + 1 by
    push_cast; ring]
  rw [glue_not_mem]
  rw [site1_mem_box_iff]
  omega

theorem matrix_pow_apply_walk {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (A : Matrix E E R) :
    ∀ (n : ℕ) (i j : E),
      (A ^ n) i j =
        ∑ p : Fin n → E,
          (if (Fin.cons i p : Fin (n + 1) → E) (Fin.last n) = j then (1 : R) else 0) *
            ∏ k : Fin n, A ((Fin.cons i p : Fin (n + 1) → E) k.castSucc) (p k) := by
  intro n
  induction n with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply, Fin.prod_univ_zero, mul_one]
    rw [Fintype.sum_unique]
    simp [Fin.last]
  | succ n ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih _ j, Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => E)]
    have hcE : ∀ (x : E × (Fin n → E)),
        (Fin.consEquiv (fun _ : Fin (n + 1) => E)) x = Fin.cons x.1 x.2 := fun _ => rfl
    refine Finset.sum_congr rfl (fun x _ => ?_)
    obtain ⟨a, q⟩ := x
    rw [hcE]
    rw [Fin.prod_univ_succ]
    have hcond : (Fin.cons i (Fin.cons a q) : Fin (n + 2) → E) (Fin.last (n + 1))
        = (Fin.cons a q : Fin (n + 1) → E) (Fin.last n) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    rw [hcond]
    simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
    ring

end StatMech.FrontierB
