import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic
/-!
Confluent (two-node) Vandermonde determinants and the column transforms used by the sympy
`vandermonde` lemmas: forward-difference column operations, the `(1 - λ)` / `(x - λ)` transforms,
and the general block determinant
`det [j^i x₁^j (i<d); j^i x₂^j (i<m-d)] = x₂^C(m-d,2) x₁^C(d,2) (x₂-x₁)^(d(m-d)) ∏ i! ∏ i!`.
-/
open Finset Nat

namespace Vandermonde
open Matrix in
theorem shift_det {n : ℕ} {δ : ℝ} :
  (Matrix.of fun (i j : Fin n) => ((j : ℝ) + δ) ^ (i : ℕ)).det = ∏ i : Fin n, ((i : ℕ)! : ℝ) := by
  rw [← Matrix.det_transpose]
  have h : (Matrix.of fun (i j : Fin n) => ((j : ℝ) + δ) ^ (i : ℕ)).transpose = Matrix.vandermonde fun j : Fin n => (j : ℝ) + δ := by
    ext i j
    simp [Matrix.vandermonde]
  have hc : ∏ x : Fin n, ∏ y ∈ Finset.Ioi x, (((y : ℕ) : ℝ) + δ - (((x : ℕ) : ℝ) + δ)) = ∏ y : Fin n, ∏ x ∈ Finset.Iio y, (((y : ℕ) : ℝ) + δ - (((x : ℕ) : ℝ) + δ)) :=
    Finset.prod_comm' (by intro x y; simp)
  rw [h, Matrix.det_vandermonde, hc]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : ∀ m : ℕ, ∏ j ∈ Finset.range m, ((m : ℝ) - j) = (m ! : ℝ) := by
    intro m
    rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← Finset.prod_range_reflect (fun j => ((j + 1 : ℕ) : ℝ)) m]
    refine Finset.prod_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← e, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp

theorem col_transformation {d m : ℕ} {x δ : ℝ} :
    (Matrix.of fun (i : Fin d) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-x) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0)) = 0 := by
  ext i j
  have hj := j.isLt
  have hi := i.isLt
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ k * ((k : ℝ) + δ) ^ (i : ℕ) *
      ((-x) ^ ((d : ℤ) + (j : ℕ) - (k : ℤ)) * (if (j : ℕ) ≤ k then (d.choose (k - j) : ℝ) else 0))) m]
  rw [← Finset.sum_subset (s₁ := Finset.Ico (j : ℕ) (j + d + 1)) (by intro k hk; simp at hk ⊢; omega) (by
      intro k _ hk'
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk'
      rcases hk' with h | h
      · rw [if_neg (by omega), mul_zero, mul_zero]
      · rw [if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero])]
  rw [Finset.sum_Ico_eq_sum_range, show (j : ℕ) + d + 1 - j = d + 1 by omega]
  have key : ∀ t ∈ Finset.range (d + 1), x ^ ((j : ℕ) + t) * ((((j : ℕ) + t : ℕ) : ℝ) + δ) ^ (i : ℕ) *
      ((-x) ^ ((d : ℤ) + (j : ℕ) - (((j : ℕ) + t : ℕ) : ℤ)) * (if (j : ℕ) ≤ (j : ℕ) + t then (d.choose ((j : ℕ) + t - j) : ℝ) else 0)) =
      x ^ ((j : ℕ) + d) * (((-1 : ℤ) ^ (d - t) * ((d.choose t : ℕ) : ℤ)) • (fun r : ℝ => r ^ (i : ℕ)) (((j : ℝ) + δ) + t • (1 : ℝ))) := by
    intro t ht
    have ht := Finset.mem_range.mp ht
    rw [if_pos (by omega), Nat.add_sub_cancel_left,
      show ((d : ℤ) + ((j : ℕ) : ℤ) - (((j : ℕ) + t : ℕ) : ℤ)) = ((d - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ d)]; ring,
      zpow_natCast, neg_pow, show x ^ ((j : ℕ) + d) = x ^ ((j : ℕ) + t) * x ^ (d - t) by rw [← pow_add]; congr 1; omega,
      zsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum,
    ← fwdDiff_iter_eq_sum_shift (h := (1 : ℝ)) (fun r : ℝ => r ^ (i : ℕ)) d ((j : ℝ) + δ),
    fwdDiff_iter_pow_eq_zero_of_lt (by omega : (i : ℕ) < d), Pi.zero_apply, mul_zero]


theorem col_transform {n m d : ℕ} {x δ l : ℝ} :
    (Matrix.of fun (i : Fin n) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0)) =
    (Matrix.of fun (i j : Fin n) => ((i : ℕ).choose j : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h * (h : ℝ) ^ ((i : ℤ) - (j : ℕ))) *
    (Matrix.of fun (i : Fin n) (j : Fin (m - d)) => ((j : ℝ) + δ) ^ (i : ℕ) * x ^ (j : ℕ)) := by
  ext i j
  have hj := j.isLt
  have hi := i.isLt
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ k * ((k : ℝ) + δ) ^ (i : ℕ) *
      ((-l) ^ ((d : ℤ) + (j : ℕ) - (k : ℤ)) * (if (j : ℕ) ≤ k then (d.choose (k - j) : ℝ) else 0))) m,
    Fin.sum_univ_eq_sum_range (fun k => (((i : ℕ).choose k : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h * (h : ℝ) ^ ((i : ℤ) - (k : ℤ))) *
      ((((j : ℕ) : ℝ) + δ) ^ k * x ^ (j : ℕ))) n]
  rw [← Finset.sum_subset (s₁ := Finset.Ico (j : ℕ) (j + d + 1)) (s₂ := Finset.range m) (by intro k hk; simp at hk ⊢; omega) (by
      intro k _ hk'
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk'
      rcases hk' with h | h
      · rw [if_neg (by omega), mul_zero, mul_zero]
      · rw [if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero])]
  rw [← Finset.sum_subset (s₁ := Finset.range ((i : ℕ) + 1)) (s₂ := Finset.range n) (by intro k hk; simp at hk ⊢; omega) (by
      intro k _ hk'
      simp only [Finset.mem_range, not_lt] at hk'
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul])]
  rw [Finset.sum_Ico_eq_sum_range, show (j : ℕ) + d + 1 - j = d + 1 by omega]
  have R : ∀ k ∈ Finset.range ((i : ℕ) + 1), (((i : ℕ).choose k : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h * (h : ℝ) ^ ((i : ℤ) - (k : ℤ))) *
      ((((j : ℕ) : ℝ) + δ) ^ k * x ^ (j : ℕ)) =
      ∑ h ∈ Finset.range (d + 1), x ^ (j : ℕ) * ((d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h *
        ((((j : ℕ) : ℝ) + δ) ^ k * (h : ℝ) ^ ((i : ℕ) - k) * ((i : ℕ).choose k : ℝ))) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [show ((i : ℤ) - (k : ℤ)) = (((i : ℕ) - k : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : k ≤ (i : ℕ))]; ring,
      zpow_natCast]
    ring
  rw [Finset.sum_congr rfl R, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← add_pow, if_pos (by omega), Nat.add_sub_cancel_left,
    show ((d : ℤ) + ((j : ℕ) : ℤ) - (((j : ℕ) + t : ℕ) : ℤ)) = ((d - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ d)]; ring,
    zpow_natCast, pow_add]
  push_cast
  ring

theorem row_transform {n m d : ℕ} {x δ l : ℝ} :
    (Matrix.of fun (i : Fin (m - d)) (j : Fin m) =>
      (-l) ^ ((d : ℤ) + (i : ℕ) - (j : ℕ)) * (if (i : ℕ) ≤ j then (d.choose ((j : ℕ) - i) : ℝ) else 0)) *
    (Matrix.of fun (i : Fin m) (j : Fin n) => x ^ (i : ℕ) * ((i : ℝ) + δ) ^ (j : ℕ)) =
    (Matrix.of fun (i : Fin (m - d)) (j : Fin n) => ((i : ℝ) + δ) ^ (j : ℕ) * x ^ (i : ℕ)) *
    (Matrix.of fun (i j : Fin n) => ((j : ℕ).choose i : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h * (h : ℝ) ^ ((j : ℤ) - (i : ℕ))) := by
  have := congrArg Matrix.transpose (col_transform (n := n) (m := m) (d := d) (x := x) (δ := δ) (l := l))
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at this
  convert this using 2 <;> (ext a b; rfl)

theorem col_transform_S {n m d : ℕ} {δ l : ℝ} :
    (Matrix.of fun (i : Fin n) (j : Fin m) => ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0)) =
    (Matrix.of fun (i j : Fin n) => ((i : ℕ).choose j : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * (h : ℝ) ^ ((i : ℤ) - (j : ℕ))) *
    (Matrix.of fun (i : Fin n) (j : Fin (m - d)) => ((j : ℝ) + δ) ^ (i : ℕ)) := by
  simpa only [one_pow, one_mul, mul_one] using col_transform (n := n) (m := m) (d := d) (x := 1) (δ := δ) (l := l)

theorem det_lower_diag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : ∀ i j : Fin n, i < j → M i j = 0) :
    M.det = ∏ i, M i i :=
  Matrix.det_of_isLowerTriangular M fun i j hij => h i j hij

theorem det_S {m d : ℕ} {δ l : ℝ} :
    ((Matrix.of fun (i : Fin (m - d)) (j : Fin m) => ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0))).det =
    (1 - l) ^ (d * (m - d)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
  rw [col_transform_S, Matrix.det_mul, shift_det, det_lower_diag, Fin.prod_univ_eq_prod_range (fun i => (i ! : ℝ)) (m - d)]
  · congr 1
    simp only [Matrix.of_apply, Nat.choose_self, Nat.cast_one, one_mul, sub_self, zpow_zero, mul_one]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    congr 1
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  · intro i j hij
    simp only [Matrix.of_apply]
    rw [Nat.choose_eq_zero_of_lt (show (i : ℕ) < j from hij), Nat.cast_zero, zero_mul]

theorem det_x {m d : ℕ} {x δ l : ℝ} :
    ((Matrix.of fun (i : Fin (m - d)) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0))).det =
    x ^ ((m - d).choose 2) * (x - l) ^ (d * (m - d)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
  rw [col_transform, Matrix.det_mul, det_lower_diag]
  · have hD : (Matrix.of fun (i : Fin (m - d)) (j : Fin (m - d)) => ((j : ℝ) + δ) ^ (i : ℕ) * x ^ (j : ℕ)) =
        (Matrix.of fun (i j : Fin (m - d)) => ((j : ℝ) + δ) ^ (i : ℕ)) * (Matrix.diagonal (fun j : Fin (m - d) => x ^ (j : ℕ)) : Matrix (Fin (m - d)) (Fin (m - d)) ℝ) := by
      ext i j
      simp [Matrix.mul_diagonal]
    rw [hD, Matrix.det_mul, shift_det, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum,
      Fin.sum_univ_eq_sum_range (fun i => i) (m - d), Finset.sum_range_id, ← Nat.choose_two_right,
      Fin.prod_univ_eq_prod_range (fun i => (i ! : ℝ)) (m - d)]
    simp only [Matrix.of_apply, Nat.choose_self, Nat.cast_one, one_mul, sub_self, zpow_zero, mul_one]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    have e : ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h = (x - l) ^ d := by
      rw [sub_eq_add_neg, add_pow]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    rw [e]
    ring
  · intro i j hij
    simp only [Matrix.of_apply]
    rw [Nat.choose_eq_zero_of_lt (show (i : ℕ) < j from hij), Nat.cast_zero, zero_mul]

theorem left_entry {d m : ℕ} {x δ : ℝ} (h : d ≤ m) (i j : Fin d) :
    ((Matrix.of fun (i : Fin d) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (k : Fin m) (j : Fin d) => (-x) ^ ((j : ℤ) - (k : ℕ)) * ((j : ℕ).choose k : ℝ))) i j =
    x ^ (j : ℕ) * (fwdDiff (1 : ℝ))^[j] (fun r : ℝ => r ^ (i : ℕ)) δ := by
  have hj := j.isLt
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ k * ((k : ℝ) + δ) ^ (i : ℕ) * ((-x) ^ (((j : ℕ) : ℤ) - (k : ℤ)) * ((j : ℕ).choose k : ℝ))) m]
  rw [← Finset.sum_subset (s₁ := Finset.range ((j : ℕ) + 1)) (s₂ := Finset.range m) (by intro k hk; simp at hk ⊢; omega) (by
      intro k _ hk'
      simp only [Finset.mem_range, not_lt] at hk'
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero])]
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  rw [show (((j : ℕ) : ℤ) - (t : ℤ)) = (((j : ℕ) - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ (j : ℕ))]; ring,
    zpow_natCast, neg_pow, show x ^ (j : ℕ) = x ^ t * x ^ ((j : ℕ) - t) by rw [← pow_add]; congr 1; omega,
    zsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem det_left {d m : ℕ} {x δ : ℝ} (h : d ≤ m) :
    ((Matrix.of fun (i : Fin d) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (k : Fin m) (j : Fin d) => (-x) ^ ((j : ℤ) - (k : ℕ)) * ((j : ℕ).choose k : ℝ))).det =
    x ^ (d.choose 2) * ∏ i ∈ Finset.range d, (i ! : ℝ) := by
  rw [det_lower_diag]
  · simp only [left_entry h, fwdDiff_iter_eq_factorial, Pi.natCast_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Fin.sum_univ_eq_sum_range (fun i => i) d, Finset.sum_range_id, ← Nat.choose_two_right,
      Fin.prod_univ_eq_prod_range (fun i => (i ! : ℝ)) d]
  · intro i j hij
    rw [left_entry h, fwdDiff_iter_pow_eq_zero_of_lt (show (i : ℕ) < j from hij), Pi.zero_apply, mul_zero]

theorem confluent_det {d m : ℕ} {x₁ x₂ : ℝ} (h : d ≤ m) :
    (Matrix.of fun (a j : Fin m) =>
      if (a : ℕ) < d then (j : ℝ) ^ (a : ℕ) * x₁ ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - d) * x₂ ^ (j : ℕ)).det =
    x₂ ^ ((m - d).choose 2) * x₁ ^ (d.choose 2) * (x₂ - x₁) ^ (d * (m - d)) *
      (∏ i ∈ Finset.range d, (i ! : ℝ)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
  set M := Matrix.of fun (a j : Fin m) =>
      if (a : ℕ) < d then (j : ℝ) ^ (a : ℕ) * x₁ ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - d) * x₂ ^ (j : ℕ) with hM
  set e : Fin d ⊕ Fin (m - d) ≃ Fin m := finSumFinEquiv.trans (finCongr (by omega : d + (m - d) = m)) with he
  set A₁ := Matrix.of fun (i : Fin d) (j : Fin m) => x₁ ^ (j : ℕ) * ((j : ℝ) + 0) ^ (i : ℕ) with hA₁
  set A₂ := Matrix.of fun (i : Fin (m - d)) (j : Fin m) => x₂ ^ (j : ℕ) * ((j : ℝ) + 0) ^ (i : ℕ) with hA₂
  set B₁ := Matrix.of fun (k : Fin m) (j : Fin d) => (-x₁) ^ ((j : ℤ) - (k : ℕ)) * ((j : ℕ).choose k : ℝ) with hB₁
  set B₂ := Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-x₁) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0) with hB₂
  set T := Matrix.fromCols B₁ B₂ with hT
  have he1 : ∀ c : Fin m, ∀ hc : (c : ℕ) < d, e.symm c = Sum.inl ⟨c, hc⟩ := by
    intro c hc
    rw [Equiv.symm_apply_eq]
    ext
    simp [he]
  have he2 : ∀ c : Fin m, ∀ hc : ¬ (c : ℕ) < d, e.symm c = Sum.inr ⟨c - d, by omega⟩ := by
    intro c hc
    rw [Equiv.symm_apply_eq]
    ext
    simp [he]
    omega
  have hrows : M.submatrix e id = Matrix.fromRows A₁ A₂ := by
    ext (a | a) j
    · simp [hM, he, hA₁, mul_comm, Fin.is_lt]
    · simp [hM, he, hA₂, mul_comm]
  have h5 : (M.submatrix e id) * T = (M.submatrix e e) * (T.submatrix e id) := by
    rw [Matrix.submatrix_mul_equiv]
    rfl
  have hT1 : (T.submatrix e id).det = 1 := by
    rw [← Matrix.det_submatrix_equiv_self e.symm, Matrix.submatrix_submatrix]
    simp only [Equiv.self_comp_symm, Function.id_comp]
    rw [Matrix.det_of_isUpperTriangular]
    · refine Finset.prod_eq_one fun c _ => ?_
      simp only [Matrix.submatrix_apply, id]
      by_cases hc : (c : ℕ) < d
      · rw [he1 c hc, hT, Matrix.fromCols_apply_inl, hB₁, Matrix.of_apply]
        simp
      · rw [he2 c hc, hT, Matrix.fromCols_apply_inr, hB₂, Matrix.of_apply]
        have hcd : ((d : ℤ) + ((c - d : ℕ) : ℤ) - (c : ℤ)) = 0 := by push_cast [Nat.cast_sub (by omega : d ≤ (c : ℕ))]; ring
        simp only [hcd, zpow_zero, one_mul]
        rw [if_pos (by omega), show (c : ℕ) - ((c : ℕ) - d) = d by omega, Nat.choose_self, Nat.cast_one]
    · intro k c hkc
      have hkc : (c : ℕ) < k := hkc
      simp only [Matrix.submatrix_apply, id]
      by_cases hc : (c : ℕ) < d
      · rw [he1 c hc, hT, Matrix.fromCols_apply_inl, hB₁, Matrix.of_apply]
        simp only
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
      · rw [he2 c hc, hT, Matrix.fromCols_apply_inr, hB₂, Matrix.of_apply]
        simp only
        rw [if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
  have hmain := congrArg Matrix.det h5
  rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self, hT1, mul_one, hrows, hT, Matrix.fromRows_mul_fromCols] at hmain
  have hz : A₁ * B₂ = 0 := by
    rw [hA₁, hB₂]
    exact col_transformation
  rw [hz, Matrix.det_fromBlocks_zero₁₂, hA₁, hB₁, det_left h, hA₂, hB₂, det_x] at hmain
  rw [← hmain]
  ring


theorem det_ratio {m d : ℕ} {r : ℝ} (h : m > d) :
    (Matrix.of fun (a j : Fin m) => if (a : ℕ) < d then (j : ℝ) ^ (a : ℕ) * r ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - d)).det =
    r ^ (d.choose 2) * (1 - r) ^ (d * (m - d)) * (∏ i ∈ Finset.range d, (i ! : ℝ)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
  have := confluent_det (d := d) (m := m) (x₁ := r) (x₂ := 1) (by omega)
  simp only [one_pow, mul_one, one_mul] at this
  rw [this]

theorem det_cons_pow {n : ℕ} {r : ℝ} :
    (Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => r ^ (j : ℕ)) (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ)))).det =
    (1 - r) ^ n * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
  have hM : Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => r ^ (j : ℕ)) (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ))) =
      Matrix.of fun (a j : Fin (n + 1)) => if (a : ℕ) < 1 then (j : ℝ) ^ (a : ℕ) * r ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - 1) * (1 : ℝ) ^ (j : ℕ) := by
    ext a j
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  rw [hM, confluent_det (by omega), show (1 : ℕ).choose 2 = 0 by decide, show n + 1 - 1 = n by omega,
    show ∏ i ∈ Finset.range 1, (i ! : ℝ) = 1 by norm_num [Finset.prod_range_succ]]
  ring

theorem det_n2 {n : ℕ} {x₁ x₂ : ℝ} :
    (Matrix.of (Matrix.vecCons (fun j : Fin (n + 2) => x₁ ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 2) => (j : ℝ) * x₁ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 2)) => (j : ℝ) ^ (i : ℕ) * x₂ ^ (j : ℕ))))).det =
    x₁ * x₂ ^ (n.choose 2) * (x₂ - x₁) ^ (2 * n) * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
  have hM : Matrix.of (Matrix.vecCons (fun j : Fin (n + 2) => x₁ ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 2) => (j : ℝ) * x₁ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 2)) => (j : ℝ) ^ (i : ℕ) * x₂ ^ (j : ℕ)))) =
      Matrix.of fun (a j : Fin (n + 2)) => if (a : ℕ) < 2 then (j : ℝ) ^ (a : ℕ) * x₁ ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - 2) * x₂ ^ (j : ℕ) := by
    ext a j
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;> simp
  rw [hM, confluent_det (by omega), show (2 : ℕ).choose 2 = 1 by decide, show n + 2 - 2 = n by omega,
    show ∏ i ∈ Finset.range 2, (i ! : ℝ) = 1 by norm_num [Finset.prod_range_succ]]
  ring

theorem det_n1 {n : ℕ} {x₁ x₂ : ℝ} :
    (Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => x₂ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ) * x₁ ^ (j : ℕ)))).det =
    x₁ ^ (n.choose 2) * (x₁ - x₂) ^ n * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
  have hM : Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => x₂ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ) * x₁ ^ (j : ℕ))) =
      Matrix.of fun (a j : Fin (n + 1)) => if (a : ℕ) < 1 then (j : ℝ) ^ (a : ℕ) * x₂ ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - 1) * x₁ ^ (j : ℕ) := by
    ext a j
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  rw [hM, confluent_det (by omega), show (1 : ℕ).choose 2 = 0 by decide, show n + 1 - 1 = n by omega,
    show ∏ i ∈ Finset.range 1, (i ! : ℝ) = 1 by norm_num [Finset.prod_range_succ]]
  ring

theorem det_n3 {n : ℕ} {r : ℝ} :
    (Matrix.of (Matrix.vecCons (fun j : Fin (n + 3) => r ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 3) => (j : ℝ) * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 3) => (j : ℝ) ^ 2 * r ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 3)) => (j : ℝ) ^ (i : ℕ)))))).det =
    2 * r ^ 3 * (1 - r) ^ (3 * n) * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
  have hM : Matrix.of (Matrix.vecCons (fun j : Fin (n + 3) => r ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 3) => (j : ℝ) * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 3) => (j : ℝ) ^ 2 * r ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 3)) => (j : ℝ) ^ (i : ℕ))))) =
      Matrix.of fun (a j : Fin (n + 3)) => if (a : ℕ) < 3 then (j : ℝ) ^ (a : ℕ) * r ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - 3) * (1 : ℝ) ^ (j : ℕ) := by
    ext a j
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a) a <;>
      simp [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
  rw [hM, confluent_det (by omega), show (3 : ℕ).choose 2 = 3 by decide, show n + 3 - 3 = n by omega,
    show ∏ i ∈ Finset.range 3, (i ! : ℝ) = 2 by norm_num [Finset.prod_range_succ, Nat.factorial]]
  ring

theorem det_n4 {n : ℕ} {r : ℝ} :
    (Matrix.of (Matrix.vecCons (fun j : Fin (n + 4) => r ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) ^ 2 * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) ^ 3 * r ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 4)) => (j : ℝ) ^ (i : ℕ))))))).det =
    12 * r ^ (Nat.choose 4 2) * (1 - r) ^ (4 * n) * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
  have hM : Matrix.of (Matrix.vecCons (fun j : Fin (n + 4) => r ^ (j : ℕ)) (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) ^ 2 * r ^ (j : ℕ))
      (Matrix.vecCons (fun j : Fin (n + 4) => (j : ℝ) ^ 3 * r ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 4)) => (j : ℝ) ^ (i : ℕ)))))) =
      Matrix.of fun (a j : Fin (n + 4)) => if (a : ℕ) < 4 then (j : ℝ) ^ (a : ℕ) * r ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - 4) * (1 : ℝ) ^ (j : ℕ) := by
    ext a j
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a) a) a <;>
      simp [Nat.mod_eq_of_lt (show 2 < n + 4 by omega), Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
  rw [hM, confluent_det (by omega), show n + 4 - 4 = n by omega,
    show ∏ i ∈ Finset.range 4, (i ! : ℝ) = 12 by norm_num [Finset.prod_range_succ, Nat.factorial]]
  ring

theorem det_powAdd {n : ℕ} {r : ℝ} :
    (Matrix.of fun (a j : Fin n) => if (a : ℕ) = 0 then 1 - r ^ ((j : ℕ) + 1) else ((j : ℝ) + 1) ^ (a : ℕ)).det =
    (1 - r) ^ n * ∏ i ∈ Finset.range n, (i ! : ℝ) := by
  cases n with
  | zero => simp
  | succ k =>
    set V := Matrix.of fun (a j : Fin (k + 1)) => ((j : ℝ) + 1) ^ (a : ℕ) with hV
    set w : Fin (k + 1) → ℝ := fun j => r ^ ((j : ℕ) + 1) with hw
    have hM : (Matrix.of fun (a j : Fin (k + 1)) => if (a : ℕ) = 0 then 1 - r ^ ((j : ℕ) + 1) else ((j : ℝ) + 1) ^ (a : ℕ)) =
        V.updateRow 0 (V 0 + (-1 : ℝ) • w) := by
      ext a j
      refine Fin.cases ?_ (fun a => ?_) a
      · simp [hV, hw]
        ring
      · simp [hV, hw]
    rw [hM, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
    have hN := det_cons_pow (n := k + 1) (r := r)
    set N := Matrix.of (Matrix.vecCons (fun j : Fin (k + 1 + 1) => r ^ (j : ℕ))
      (fun (i : Fin (k + 1)) (j : Fin (k + 1 + 1)) => (j : ℝ) ^ (i : ℕ))) with hNdef
    have e0 : N.submatrix (Fin.succAbove 0) Fin.succ = V := by
      ext a j
      simp [hNdef, hV]
    have e1 : N.submatrix (Fin.succAbove (Fin.succ 0)) Fin.succ = V.updateRow 0 w := by
      ext a j
      refine Fin.cases ?_ (fun a => ?_) a
      · simp [hNdef, hV, hw]
      · simp [hNdef, hV, hw]
    have hrest : ∑ i : Fin k, (-1 : ℝ) ^ ((Fin.succ (Fin.succ i) : Fin (k + 1 + 1)) : ℕ) * N (Fin.succ (Fin.succ i)) 0 *
        (N.submatrix (Fin.succAbove (Fin.succ (Fin.succ i))) Fin.succ).det = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [hNdef]
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, hrest, e0, e1] at hN
    rw [← hN]
    simp [hNdef]

end Vandermonde
