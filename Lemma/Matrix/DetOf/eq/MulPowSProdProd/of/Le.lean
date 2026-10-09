import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.MulOfPowAddOfPowNegChoose.eq.Zero
import Lemma.Matrix.DetMulOfMulPowOfPowNegChoose.eq.MulMulPowPowSubProd
import Lemma.Matrix.DetMulOfOfPowNegChoose.eq.MulPowProd.of.Le
open Matrix Nat


@[path]
private lemma main
  {d m : ℕ}
  {x₁ x₂ : ℝ}
-- given
  (h : d ≤ m) :
-- imply
  (Matrix.of fun (a j : Fin m) =>
      if (a : ℕ) < d then (j : ℝ) ^ (a : ℕ) * x₁ ^ (j : ℕ) else (j : ℝ) ^ ((a : ℕ) - d) * x₂ ^ (j : ℕ)).det =
    x₂ ^ ((m - d).choose 2) * x₁ ^ (d.choose 2) * (x₂ - x₁) ^ (d * (m - d)) *
      (∏ i ∈ Finset.range d, (i ! : ℝ)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
-- proof
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
    ·
      refine Finset.prod_eq_one fun c _ => ?_
      simp only [Matrix.submatrix_apply, id]
      if hc : (c : ℕ) < d then
        rw [he1 c hc, hT, Matrix.fromCols_apply_inl, hB₁, Matrix.of_apply]
        simp
      else
        rw [he2 c hc, hT, Matrix.fromCols_apply_inr, hB₂, Matrix.of_apply]
        have hcd : ((d : ℤ) + ((c - d : ℕ) : ℤ) - (c : ℤ)) = 0 := by push_cast [Nat.cast_sub (by omega : d ≤ (c : ℕ))]; ring
        simp only [hcd, zpow_zero, one_mul]
        rw [if_pos (by omega), show (c : ℕ) - ((c : ℕ) - d) = d by omega, Nat.choose_self, Nat.cast_one]
    ·
      intro k c hkc
      have hkc : (c : ℕ) < k := hkc
      simp only [Matrix.submatrix_apply, id]
      if hc : (c : ℕ) < d then
        rw [he1 c hc, hT, Matrix.fromCols_apply_inl, hB₁, Matrix.of_apply]
        simp only
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
      else
        rw [he2 c hc, hT, Matrix.fromCols_apply_inr, hB₂, Matrix.of_apply]
        simp only
        rw [if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
  have hmain := congrArg Matrix.det h5
  rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self, hT1, mul_one, hrows, hT, Matrix.fromRows_mul_fromCols] at hmain
  have hz : A₁ * B₂ = 0 := by
    rw [hA₁, hB₂]
    exact MulOfPowAddOfPowNegChoose.eq.Zero
  rw [hz, Matrix.det_fromBlocks_zero₁₂, hA₁, hB₁, DetMulOfOfPowNegChoose.eq.MulPowProd.of.Le h, hA₂, hB₂, DetMulOfMulPowOfPowNegChoose.eq.MulMulPowPowSubProd] at hmain
  rw [← hmain]
  ring


-- created on 2026-10-07
