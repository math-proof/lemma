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
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part15
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma openMatrixProduct_eq_nat {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a b : E) {m : ℕ} (q : Fin m → E) :
    openMatrixProduct A a b q = openMatrixProductNat A a b q := by
  rw [openMatrixProduct, openMatrixProductNat, Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  simp only [hk, dite_true]
  rw [fullPath_eq_pathVertex, snoc_eq_pathVertex_succ a b q]
  rfl

lemma pathVertex_center_left {E : Type*} (a s b : E) (n k : ℕ)
    (l r : Fin n → E) (hk : k ≤ n + 1) :
    pathVertex a b (centerPathEquiv E n (s,(l,r))) k =
      pathVertex a s l k := by
  by_cases h0 : k = 0
  · simp [pathVertex, h0]
  by_cases hn : k ≤ n
  · have hbig : k ≤ 2 * n + 1 := by omega
    simp only [pathVertex, h0, hn, hbig, dite_false, dite_true]
    exact centerPathEquiv_left E n s l r ⟨k - 1, by omega⟩
  · have hkn : k = n + 1 := by omega
    subst k
    have hbig : n + 1 ≤ 2 * n + 1 := by omega
    simp only [pathVertex, hbig, hn, dite_true, dite_false]
    simpa using centerPathEquiv_center E n s l r

lemma pathVertex_center_right {E : Type*} (a s b : E) (n k : ℕ)
    (l r : Fin n → E) (hk : k ≤ n + 1) :
    pathVertex a b (centerPathEquiv E n (s,(l,r))) (n + 1 + k) =
      pathVertex s b r k := by
  by_cases h0 : k = 0
  · subst k
    rw [pathVertex, pathVertex, dif_neg (by omega),
      dif_pos (by omega : n + 1 ≤ 2 * n + 1), dif_pos (by omega)]
    simpa using centerPathEquiv_center E n s l r
  by_cases hn : k ≤ n
  · rw [pathVertex, pathVertex, dif_neg (by omega), dif_neg h0,
      dif_pos (by omega : n + 1 + k ≤ 2 * n + 1), dif_pos hn]
    simpa only [show n + 1 + k - 1 = n + 1 + (k - 1) by omega] using
      centerPathEquiv_right E n s l r ⟨k - 1, by omega⟩
  · have hkn : k = n + 1 := by omega
    subst k
    rw [pathVertex, pathVertex, dif_neg (by omega), dif_neg (by omega),
      dif_neg (by omega), dif_neg (by omega)]

theorem openMatrixProduct_center_factor {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a s b : E) (n : ℕ)
    (l r : Fin n → E) :
    openMatrixProduct A a b (centerPathEquiv E n (s,(l,r))) =
      openMatrixProduct A a s l * openMatrixProduct A s b r := by
  rw [openMatrixProduct_eq_nat, openMatrixProduct_eq_nat,
    openMatrixProduct_eq_nat]
  unfold openMatrixProductNat
  conv_lhs =>
    rw [show 2 * n + 1 + 1 = (n + 1) + (n + 1) by omega]
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [pathVertex_center_left a s b n k l r (by omega),
      pathVertex_center_left a s b n (k + 1) l r (by omega)]
  · apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [pathVertex_center_right a s b n k l r (by omega)]
    rw [show n + 1 + k + 1 = n + 1 + (k + 1) by omega]
    rw [pathVertex_center_right a s b n (k + 1) l r (by omega)]

theorem sum_openMatrixProduct_center {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a s b : E) (n : ℕ) :
    (∑ q : Fin (2 * n + 1) → E,
      if q ⟨n, by omega⟩ = s then openMatrixProduct A a b q else 0) =
        (A ^ (n + 1)) a s * (A ^ (n + 1)) s b := by
  rw [← Equiv.sum_comp (centerPathEquiv E n)
    (fun q => if q ⟨n, by omega⟩ = s then openMatrixProduct A a b q else 0)]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [centerPathEquiv_center]
  rw [Finset.sum_eq_single s]
  · simp_rw [openMatrixProduct_center_factor]
    simp only [if_true]
    rw [← Finset.sum_mul_sum]
    rw [← matrix_pow_apply_eq_sum_open, ← matrix_pow_apply_eq_sum_open]
  · intro c hc hcs
    simp [hcs]
  · simp


lemma interiorStateEquiv_center
    (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    interiorStateEquiv n tau ⟨n, by omega⟩ = fvPathState eta n tau (n + 1) := by
  exact interiorStateEquiv_apply eta n tau ⟨n, by omega⟩

theorem sum_fvTransferProduct_center_eq_matrix_pow
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) (s : Fin 2) :
    (∑ tau : {x // x ∈ box 1 n} → Bool,
      if fvPathState eta n tau (n + 1) = s then
        fvTransferProduct eta n tau beta h else 0) =
      (isingTransferReal beta (beta * h) ^ (n + 1))
          (fvLeftBoundaryState eta n) s *
        (isingTransferReal beta (beta * h) ^ (n + 1))
          s (fvRightBoundaryState eta n) := by
  calc
    _ = ∑ tau : {x // x ∈ box 1 n} → Bool,
        if interiorStateEquiv n tau ⟨n, by omega⟩ = s then
          openMatrixProduct (isingTransferReal beta (beta * h))
            (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n)
            (interiorStateEquiv n tau) else 0 := by
      apply Finset.sum_congr rfl
      intro tau htau
      rw [interiorStateEquiv_center eta n tau,
        fvTransferProduct_eq_openMatrixProduct]
    _ = ∑ q : Fin (2 * n + 1) → Fin 2,
        if q ⟨n, by omega⟩ = s then
          openMatrixProduct (isingTransferReal beta (beta * h))
            (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) q else 0 :=
      by
        simpa only using (Equiv.sum_comp (interiorStateEquiv n)
          (fun q : Fin (2 * n + 1) → Fin 2 =>
            if q (⟨n, by omega⟩ : Fin (2 * n + 1)) = s then
              (openMatrixProduct (isingTransferReal beta (beta * h))
                (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) q)
            else 0))
    _ = _ := sum_openMatrixProduct_center _ _ _ _ _


end StatMech.FrontierB
