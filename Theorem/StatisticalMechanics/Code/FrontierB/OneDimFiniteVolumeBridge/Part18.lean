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
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma splitPathEquiv_apply (E : Type*) (m n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin n → E) (k : Fin (m + n + 1)) :
    splitPathEquiv E m n (s, (l, r)) k =
      Fin.append l (Fin.cons s r) (Fin.cast (by omega) k) := by
  rfl

lemma splitPathEquiv_center (E : Type*) (m n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin n → E) :
    splitPathEquiv E m n (s, (l, r)) ⟨m, by omega⟩ = s := by
  rw [splitPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨m, by omega⟩ : Fin (m + n + 1)) =
    Fin.natAdd m (0 : Fin (n + 1)) by apply Fin.ext; simp]
  rw [Fin.append_right, Fin.cons_zero]

lemma splitPathEquiv_left (E : Type*) (m n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin n → E) (i : Fin m) :
    splitPathEquiv E m n (s, (l, r)) ⟨i.val, by omega⟩ = l i := by
  rw [splitPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨i.val, by omega⟩ : Fin (m + n + 1)) =
    Fin.castAdd (n + 1) i by apply Fin.ext; simp]
  rw [Fin.append_left]

lemma splitPathEquiv_right (E : Type*) (m n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin n → E) (i : Fin n) :
    splitPathEquiv E m n (s, (l, r)) ⟨m + 1 + i.val, by omega⟩ = r i := by
  rw [splitPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨m + 1 + i.val, by omega⟩ : Fin (m + n + 1)) =
    Fin.natAdd m (Fin.succ i) by
      apply Fin.ext
      change m + 1 + i.val = m + (i.val + 1)
      omega]
  rw [Fin.append_right, Fin.cons_succ]

lemma pathVertex_split_left {E : Type*} (a s b : E) (m n k : ℕ)
    (l : Fin m → E) (r : Fin n → E) (hk : k ≤ m + 1) :
    pathVertex a b (splitPathEquiv E m n (s, (l, r))) k =
      pathVertex a s l k := by
  by_cases h0 : k = 0
  · simp [pathVertex, h0]
  by_cases hm : k ≤ m
  · have hbig : k ≤ m + n + 1 := by omega
    simp only [pathVertex, h0, hm, hbig, dite_false, dite_true]
    exact splitPathEquiv_left E m n s l r ⟨k - 1, by omega⟩
  · have hkm : k = m + 1 := by omega
    subst k
    have hbig : m + 1 ≤ m + n + 1 := by omega
    simp only [pathVertex, hbig, hm, dite_true, dite_false]
    simpa using splitPathEquiv_center E m n s l r

lemma pathVertex_split_right {E : Type*} (a s b : E) (m n k : ℕ)
    (l : Fin m → E) (r : Fin n → E) (hk : k ≤ n + 1) :
    pathVertex a b (splitPathEquiv E m n (s, (l, r))) (m + 1 + k) =
      pathVertex s b r k := by
  by_cases h0 : k = 0
  · subst k
    rw [pathVertex, pathVertex, dif_neg (by omega),
      dif_pos (by omega : m + 1 ≤ m + n + 1), dif_pos (by omega)]
    simpa using splitPathEquiv_center E m n s l r
  by_cases hn : k ≤ n
  · rw [pathVertex, pathVertex, dif_neg (by omega), dif_neg h0,
      dif_pos (by omega : m + 1 + k ≤ m + n + 1), dif_pos hn]
    simpa only [show m + 1 + k - 1 = m + 1 + (k - 1) by omega] using
      splitPathEquiv_right E m n s l r ⟨k - 1, by omega⟩
  · have hkn : k = n + 1 := by omega
    subst k
    rw [pathVertex, pathVertex, dif_neg (by omega), dif_neg (by omega),
      dif_neg (by omega), dif_neg (by omega)]

theorem openMatrixProduct_split_factor {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a s b : E) (m n : ℕ)
    (l : Fin m → E) (r : Fin n → E) :
    openMatrixProduct A a b (splitPathEquiv E m n (s, (l, r))) =
      openMatrixProduct A a s l * openMatrixProduct A s b r := by
  rw [openMatrixProduct_eq_nat, openMatrixProduct_eq_nat, openMatrixProduct_eq_nat]
  unfold openMatrixProductNat
  conv_lhs =>
    rw [show m + n + 1 + 1 = (m + 1) + (n + 1) by omega]
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [pathVertex_split_left a s b m n k l r (by omega),
      pathVertex_split_left a s b m n (k + 1) l r (by omega)]
  · apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [pathVertex_split_right a s b m n k l r (by omega)]
    rw [show m + 1 + k + 1 = m + 1 + (k + 1) by omega]
    rw [pathVertex_split_right a s b m n (k + 1) l r (by omega)]

theorem sum_openMatrixProduct_split {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a s b : E) (m n : ℕ) :
    (∑ q : Fin (m + n + 1) → E,
      if q ⟨m, by omega⟩ = s then openMatrixProduct A a b q else 0) =
        (A ^ (m + 1)) a s * (A ^ (n + 1)) s b := by
  rw [← Equiv.sum_comp (splitPathEquiv E m n)
    (fun q => if q ⟨m, by omega⟩ = s then openMatrixProduct A a b q else 0)]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [splitPathEquiv_center]
  rw [Finset.sum_eq_single s]
  · simp_rw [openMatrixProduct_split_factor]
    simp only [if_true]
    rw [← Finset.sum_mul_sum]
    rw [← matrix_pow_apply_eq_sum_open, ← matrix_pow_apply_eq_sum_open]
  · intro c hc hcs
    simp [hcs]
  · simp


end StatMech.FrontierB
