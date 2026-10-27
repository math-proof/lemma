/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch5Entry10bEuleriansymmetry.lean -/


import Theorem.Analysis.SpecialFunctions.Part1Ch5Entry10bEuleriansymmetry.Part3
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 10b API checks

The first even Euler numbers, the defining recurrence at `m = 0`, and the Eulerian symmetry
identity at `n = 0`, `n = 1` and `n = 2`.
-/


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry

open scoped BigOperators

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry

-- The even Euler numbers start `1, -1, 5, -61`.
example : chapter5EulerEven 0 = 1 := chapter5EulerEven_zero

example : chapter5EulerEven 1 = -1 := by
  have h1 := chapter5EulerEven_step 1 (by omega)
  have c : (Nat.choose (2 * 1) (2 * 0) : ℤ) = 1 := by decide
  have v : (0 : Fin 1).val = 0 := by decide
  simp only [h1, Fin.sum_univ_one, c, v, chapter5EulerEven_zero]
  norm_num

example : chapter5EulerEven 2 = 5 := by
  have h := chapter5EulerEven_recurrence 2
  have hexp3 (f : ℕ → ℤ) : (∑ k ∈ Finset.range 3, f k) = f 0 + f 1 + f 2 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ,
      show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  have h23 : (2 + 1 : ℕ) = 3 := rfl
  have c0 : ((Nat.choose (2 * 2) (2 * 0) : ℕ) : ℤ) = 1 := by decide
  have c2 : ((Nat.choose (2 * 2) (2 * 1) : ℕ) : ℤ) = 6 := by decide
  have c4 : ((Nat.choose (2 * 2) (2 * 2) : ℕ) : ℤ) = 1 := by decide
  have e0 : chapter5EulerEven 0 = 1 := chapter5EulerEven_zero
  have e1 : chapter5EulerEven 1 = -1 := by
    have h1 := chapter5EulerEven_step 1 (by omega)
    have c : (Nat.choose (2 * 1) (2 * 0) : ℤ) = 1 := by decide
    have v : (0 : Fin 1).val = 0 := by decide
    simp only [h1, Fin.sum_univ_one, c, v, chapter5EulerEven_zero]
    norm_num
  have hne : (2 : ℕ) ≠ 0 := by omega
  simp only [h23, hexp3, c0, c2, c4, e0, e1, hne, ite_false] at h
  omega

example : chapter5EulerEven 3 = -61 := by
  have h := chapter5EulerEven_recurrence 3
  have hexp4 (f : ℕ → ℤ) :
      (∑ k ∈ Finset.range 4, f k) = f 0 + f 1 + f 2 + f 3 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, Finset.sum_range_succ,
      show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ,
      show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  have h34 : (3 + 1 : ℕ) = 4 := rfl
  have c0 : ((Nat.choose (2 * 3) (2 * 0) : ℕ) : ℤ) = 1 := by decide
  have c2 : ((Nat.choose (2 * 3) (2 * 1) : ℕ) : ℤ) = 15 := by decide
  have c4 : ((Nat.choose (2 * 3) (2 * 2) : ℕ) : ℤ) = 15 := by decide
  have c6 : ((Nat.choose (2 * 3) (2 * 3) : ℕ) : ℤ) = 1 := by decide
  have e0 : chapter5EulerEven 0 = 1 := chapter5EulerEven_zero
  have e1 : chapter5EulerEven 1 = -1 := by
    have h1 := chapter5EulerEven_step 1 (by omega)
    have c : (Nat.choose (2 * 1) (2 * 0) : ℤ) = 1 := by decide
    have v : (0 : Fin 1).val = 0 := by decide
    simp only [h1, Fin.sum_univ_one, c, v, chapter5EulerEven_zero]
    norm_num
  have e2 : chapter5EulerEven 2 = 5 := by
    have h2 := chapter5EulerEven_recurrence 2
    have hexp3 (f : ℕ → ℤ) : (∑ k ∈ Finset.range 3, f k) = f 0 + f 1 + f 2 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ,
        show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    have h23 : (2 + 1 : ℕ) = 3 := rfl
    have c0 : ((Nat.choose (2 * 2) (2 * 0) : ℕ) : ℤ) = 1 := by decide
    have c2 : ((Nat.choose (2 * 2) (2 * 1) : ℕ) : ℤ) = 6 := by decide
    have c4 : ((Nat.choose (2 * 2) (2 * 2) : ℕ) : ℤ) = 1 := by decide
    have hne : (2 : ℕ) ≠ 0 := by omega
    simp only [h23, hexp3, c0, c2, c4, e0, e1, hne, ite_false] at h2
    omega
  have hne : (3 : ℕ) ≠ 0 := by omega
  simp only [h34, hexp4, c0, c2, c4, c6, e0, e1, e2, hne, ite_false] at h
  omega

-- The recurrence at `m = 0` sums to `1`.
example : ∑ k ∈ Finset.range 1,
    ((Nat.choose (2 * 0) (2 * k) : ℕ) : ℤ) * chapter5EulerEven k = 1 := by
  have h := chapter5EulerEven_recurrence 0
  simpa using h

-- At `n = 0` both sides of the Eulerian symmetry identity vanish.
example : (2 : ℚ) ^ (2 * 0) * ((2 : ℚ) ^ (2 * 0) - 1) * bernoulli (2 * 0) = 0 := by
  rw [ramanujan_part1_ch5_entry10b_euleriansymmetry 0]
  simp

-- At `n = 1` the identity evaluates to `2`.
example : (2 : ℚ) ^ (2 * 1) * ((2 : ℚ) ^ (2 * 1) - 1) * bernoulli (2 * 1) = 2 := by
  rw [ramanujan_part1_ch5_entry10b_euleriansymmetry 1]
  have e0 : chapter5EulerEven 0 = 1 := chapter5EulerEven_zero
  have c00 : (Nat.choose (2 * 1 - 2) (2 * 0) : ℚ) = 1 := by decide
  have i0 : (1 - 0 - 1 : ℕ) = 0 := by decide
  simp only [Finset.sum_range_one, i0, c00, e0]
  norm_num

-- At `n = 2` the identity evaluates to `-8`.
example : (2 : ℚ) ^ (2 * 2) * ((2 : ℚ) ^ (2 * 2) - 1) * bernoulli (2 * 2) = -8 := by
  rw [ramanujan_part1_ch5_entry10b_euleriansymmetry 2]
  have e0 : chapter5EulerEven 0 = 1 := chapter5EulerEven_zero
  have e1 : chapter5EulerEven 1 = -1 := by
    have h1 := chapter5EulerEven_step 1 (by omega)
    have c : (Nat.choose (2 * 1) (2 * 0) : ℤ) = 1 := by decide
    have v : (0 : Fin 1).val = 0 := by decide
    simp only [h1, Fin.sum_univ_one, c, v, chapter5EulerEven_zero]
    norm_num
  have hexp2 (f : ℕ → ℚ) : (∑ k ∈ Finset.range 2, f k) = f 0 + f 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  have c0 : (Nat.choose (2 * 2 - 2) (2 * 0) : ℚ) = 1 := by decide
  have c2 : (Nat.choose (2 * 2 - 2) (2 * 1) : ℚ) = 1 := by decide
  have i0 : (2 - 0 - 1 : ℕ) = 1 := by decide
  have i1 : (2 - 1 - 1 : ℕ) = 0 := by decide
  simp only [hexp2, i0, i1, c0, c2, e0, e1]
  norm_num

end MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
