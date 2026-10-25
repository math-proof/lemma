/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part3
open Finset Matrix


namespace StatMech.FrontierD

theorem matrixChainWeight_snoc {α : Type*} [Fintype α] {k : ℕ}
    (A : Matrix α α ℝ) (a b z : α) (q : Fin k → α) :
    matrixChainWeight A (Fin.cons a (Fin.snoc q z)) b =
      matrixChainWeight A (Fin.cons a q) z * A z b := by
  rw [Fin.cons_snoc_eq_snoc_cons]
  let x : Fin (k + 1) → α := Fin.cons a q
  let y : Fin (k + 2) → α := Fin.snoc x z
  change matrixChainWeight A y b = matrixChainWeight A x z * A z b
  have hsucc (i : Fin k) : i.castSucc.succ = i.succ.castSucc := by
    ext
    rfl
  have hprod :
      ∏ i : Fin k,
          A (y i.castSucc.castSucc) (y i.castSucc.succ) =
        ∏ i : Fin k, A (x i.castSucc) (x i.succ) := by
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [y]
    rw [hsucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  simp only [matrixChainWeight, Fin.prod_univ_castSucc]
  rw [hprod]
  dsimp [y]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem matrix_pow_succ_apply_eq_sum_chain {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) (k : ℕ) (a b : α) :
    (A ^ (k + 1)) a b =
      ∑ q : Fin k → α, matrixChainWeight A (Fin.cons a q) b := by
  induction k generalizing b with
  | zero =>
      simp [matrixChainWeight]
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [ih]
      simp_rw [Finset.sum_mul]
      calc
        ∑ x, ∑ q, matrixChainWeight A (Fin.cons a q) x * A x b =
            ∑ zq : α × (Fin k → α),
              matrixChainWeight A (Fin.cons a zq.2) zq.1 * A zq.1 b :=
          (Fintype.sum_prod_type (fun zq : α × (Fin k → α) =>
            matrixChainWeight A (Fin.cons a zq.2) zq.1 * A zq.1 b)).symm
        _ = ∑ q : Fin (k + 1) → α, matrixChainWeight A (Fin.cons a q) b := by
          apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (k + 1) => α))
          intro zq
          exact (matrixChainWeight_snoc A a b zq.1 zq.2).symm

theorem matrixCycleWeight_eq_chain {α : Type*} [Fintype α]
    (A : Matrix α α ℝ) (k : ℕ) (x : Fin (k + 1) → α) :
    matrixCycleWeight (Nat.succ_pos k) A x =
      matrixChainWeight A x (x 0) := by
  rw [matrixCycleWeight, Fin.prod_univ_castSucc]
  simp only [finitePeriodicSucc_castSucc, finitePeriodicSucc_last,
    matrixChainWeight]

theorem matrixCycleWeight_sum_eq_trace_pow {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) (k : ℕ) :
    ∑ x : Fin (k + 1) → α, matrixCycleWeight (Nat.succ_pos k) A x =
      Matrix.trace (A ^ (k + 1)) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [matrix_pow_succ_apply_eq_sum_chain]
  calc
    ∑ x : Fin (k + 1) → α, matrixCycleWeight (Nat.succ_pos k) A x =
        ∑ aq : α × (Fin k → α),
          matrixChainWeight A (Fin.cons aq.1 aq.2) aq.1 := by
      symm
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => α))
      intro aq
      exact (matrixCycleWeight_eq_chain A k (Fin.cons aq.1 aq.2)).symm
    _ = ∑ a : α, ∑ q : Fin k → α,
        matrixChainWeight A (Fin.cons a q) a :=
      Fintype.sum_prod_type _


theorem matrixCompatibleCycleSum_eq_trace_pow {α : Type*} [Fintype α]
    [DecidableEq α] {M : ℕ} (hM : 0 < M) (A : Matrix α α ℝ) :
    matrixCompatibleCycleSum hM A = Matrix.trace (A ^ M) := by
  classical
  have hfilter :
      ∑ x : MatrixCompatibleCycle hM A, matrixCycleWeight hM A x =
        ∑ x : Fin M → α, matrixCycleWeight hM A x := by
    rw [← Finset.sum_subtype
      (Finset.univ.filter fun x : Fin M → α =>
        ∀ i, A (x i) (x (finitePeriodicSucc hM i)) ≠ 0) (by simp)]
    apply Finset.sum_filter_of_ne
    intro x hx hweight i hi
    apply hweight
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [matrixCompatibleCycleSum, hfilter]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  exact matrixCycleWeight_sum_eq_trace_pow A k


end StatMech.FrontierD
