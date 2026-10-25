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
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part11
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


theorem matrix_pow_apply_eq_sum_open {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (A : Matrix E E R) (a b : E) (m : ℕ) :
    (A ^ (m + 1)) a b = ∑ q : Fin m → E, openMatrixProduct A a b q := by
  rw [matrix_pow_apply_walk]
  rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (m + 1) => E)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · apply Finset.sum_congr rfl
    intro q hq
    simp only [openMatrixProduct]
    rw [show (Fin.snocEquiv fun _ : Fin (m + 1) => E) (b, q) =
      Fin.snoc q b from rfl]
    rw [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
    simp
  · intro c hc hcb
    simp [hcb]
  · simp


lemma interior_snoc_eq_path (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    Fin.snoc (interiorStateEquiv n tau) (fvRightBoundaryState eta n) =
      fun k : Fin (2 * n + 2) => fvPathState eta n tau (k.val + 1) := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · rw [Fin.snoc_last]
    simpa using (fvPathState_right eta n tau).symm
  · rw [Fin.snoc_castSucc]
    exact interiorStateEquiv_apply eta n tau i

lemma boundary_cons_snoc_eq_path (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    Fin.cons (fvLeftBoundaryState eta n)
        (Fin.snoc (interiorStateEquiv n tau) (fvRightBoundaryState eta n)) =
      fun k : Fin (2 * n + 3) => fvPathState eta n tau k.val := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · rw [Fin.cons_zero]
    simpa using (fvPathState_zero eta n tau).symm
  · rw [Fin.cons_succ, interior_snoc_eq_path]
    rfl

lemma fvTransferProduct_eq_openMatrixProduct
    (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (beta h : ℝ) :
    fvTransferProduct eta n tau beta h =
      openMatrixProduct (isingTransferReal beta (beta * h))
        (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n)
        (interiorStateEquiv n tau) := by
  rw [fvTransferProduct, openMatrixProduct, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k hk
  rw [boundary_cons_snoc_eq_path, interior_snoc_eq_path]
  rfl


lemma sum_fvTransferProduct_eq_matrix_pow
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) :
    (∑ tau : {x // x ∈ box 1 n} → Bool,
      fvTransferProduct eta n tau beta h) =
        (isingTransferReal beta (beta * h) ^ (2 * n + 2))
          (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
  calc
    (∑ tau : {x // x ∈ box 1 n} → Bool,
        fvTransferProduct eta n tau beta h) =
      ∑ tau : {x // x ∈ box 1 n} → Bool,
        openMatrixProduct (isingTransferReal beta (beta * h))
          (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n)
          (interiorStateEquiv n tau) := by
            apply Finset.sum_congr rfl
            intro tau htau
            exact fvTransferProduct_eq_openMatrixProduct eta n tau beta h
    _ = ∑ q : Fin (2 * n + 1) → Fin 2,
        openMatrixProduct (isingTransferReal beta (beta * h))
          (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) q :=
      Equiv.sum_comp (interiorStateEquiv n) _
    _ = (isingTransferReal beta (beta * h) ^ (2 * n + 2))
          (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
      exact (matrix_pow_apply_eq_sum_open _ _ _ _).symm


end StatMech.FrontierB
