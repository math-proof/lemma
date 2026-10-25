/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Euclidean/DescartesCircleTheorem.lean -/


import Lemma.Set.Euclidean.DescartesCircleTheorem


namespace MetaMathlibExt

-- The rational enclosing-circle configuration has curvatures -1/2, 1, 1, and 3/2.
example : (3 : ℝ) ^ 2 = 2 * ((-1 / 2 : ℝ) ^ 2 + 1 ^ 2 + 1 ^ 2 + (3 / 2) ^ 2) := by
  let p (x y : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![x, y]
  let c : Fin 4 → EuclideanSpace ℝ (Fin 2) :=
    ![p 0 0, p (-1) 0, p 1 0, p 0 (4 / 3)]
  let r : Fin 4 → ℝ := ![2, 1, 1, 2 / 3]
  let k : Fin 4 → ℝ := ![-1 / 2, 1, 1, 3 / 2]
  have hr : ∀ i, 0 < r i := by
    intro i
    fin_cases i <;> norm_num [r]
  have hsqrt4 : Real.sqrt 4 = 2 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt9 : Real.sqrt 9 = 3 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt16 : Real.sqrt 16 = 4 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt25 : Real.sqrt 25 = 5 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have htan : ∃ e : Fin 4, k e = -1 / r e ∧ (∀ j, j ≠ e → k j = 1 / r j) ∧
      (∀ j, j ≠ e → dist (c e) (c j) = r e - r j) ∧
      ∀ i j, i ≠ e → j ≠ e → i ≠ j → dist (c i) (c j) = r i + r j := by
    refine ⟨0, ?_, ?_, ?_, ?_⟩
    · norm_num [k, r]
    · intro j hj
      fin_cases j <;> norm_num [k, r] at *
    · intro j hj
      fin_cases j <;>
        norm_num [c, p, r, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq,
          hsqrt9, hsqrt16, hsqrt25] at *
    · intro i j hi hj hij
      fin_cases i <;> fin_cases j <;>
        norm_num [c, p, r, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq,
          hsqrt4, hsqrt9, hsqrt16, hsqrt25] at *
  have h := descartes_circle_theorem c r k hr (Or.inr htan)
  convert h using 1 <;> norm_num [k, Fin.sum_univ_four]

-- A rational all-external configuration has curvatures 2, 3, 6, and 23.
example : (34 : ℝ) ^ 2 = 2 * ((2 : ℝ) ^ 2 + 3 ^ 2 + 6 ^ 2 + 23 ^ 2) := by
  let p (x y : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![x, y]
  let c : Fin 4 → EuclideanSpace ℝ (Fin 2) :=
    ![p 0 0, p (5 / 6) 0, p (8 / 15) (2 / 5), p (117 / 230) (22 / 115)]
  let r : Fin 4 → ℝ := ![1 / 2, 1 / 3, 1 / 6, 1 / 23]
  let k : Fin 4 → ℝ := ![2, 3, 6, 23]
  have hr : ∀ i, 0 < r i := by
    intro i
    fin_cases i <;> norm_num [r]
  have hsqrt4 : Real.sqrt 4 = 2 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt9 : Real.sqrt 9 = 3 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt25 : Real.sqrt 25 = 5 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt36 : Real.sqrt 36 = 6 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt625 : Real.sqrt 625 = 25 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt676 : Real.sqrt 676 = 26 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt841 : Real.sqrt 841 = 29 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt2116 : Real.sqrt 2116 = 46 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt4761 : Real.sqrt 4761 = 69 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt19044 : Real.sqrt 19044 = 138 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  have htan : (∀ i j, i ≠ j → dist (c i) (c j) = r i + r j) ∧
      ∀ i, k i = 1 / r i := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        norm_num [c, p, r, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq,
          hsqrt4, hsqrt9, hsqrt25, hsqrt36, hsqrt625, hsqrt676, hsqrt841,
          hsqrt2116, hsqrt4761, hsqrt19044] at *
    · intro i
      fin_cases i <;> norm_num [k, r]
  have h := descartes_circle_theorem c r k hr (Or.inl htan)
  convert h using 1 <;> norm_num [k, Fin.sum_univ_four]

example (c : Fin 4 → EuclideanSpace ℝ (Fin 2)) (r : Fin 4 → ℝ)
    (hr : ∀ i, 0 < r i)
    (htan : ∀ i j, i ≠ j → dist (c i) (c j) = r i + r j)
    (hr0 : r 0 = 1 / 2) (hr1 : r 1 = 1 / 3) (hr2 : r 2 = 1 / 6) :
    r 3 = 1 / 23 := by
  let k : Fin 4 → ℝ := fun i ↦ 1 / r i
  have h := descartes_circle_theorem c r k hr (Or.inl ⟨htan, fun _ ↦ rfl⟩)
  have hk3pos : 0 < k 3 := one_div_pos.mpr (hr 3)
  have hfactor : (k 3 - 23) * (k 3 + 1) = 0 := by
    norm_num [Fin.sum_univ_four, k, hr0, hr1, hr2] at h
    rw [← inv_pow] at h
    simp only [k, one_div]
    ring_nf at h ⊢
    linarith [h]
  have hk3 : k 3 = 23 := by
    rcases mul_eq_zero.mp hfactor with h | h <;> nlinarith
  calc
    r 3 = (k 3)⁻¹ := by simp [k]
    _ = (23 : ℝ)⁻¹ := by rw [hk3]
    _ = 1 / 23 := by rw [one_div]

end MetaMathlibExt
