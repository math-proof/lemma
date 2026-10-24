import Mathlib
import sympy.Basic
open scoped BigOperators


namespace MetaMathlibExt

/--
[pow_eq_sum_stirlingSecond_mul_factorial_choose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
private lemma pow_eq_sum_stirlingSecond_mul_factorial_choose (t n : ℕ) :
  (n : ℝ) ^ t = ∑ l ∈ Finset.range (t + 1),
    (Nat.stirlingSecond t l : ℝ) * (l.factorial : ℝ) * (Nat.choose n l : ℝ) := by
  have h := congrArg (Nat.cast : ℕ → ℝ)
    (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n t)
  push_cast at h
  simpa only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fwdDiff_iter_pow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
private lemma fwdDiff_iter_pow_zero (t k : ℕ) :
  ((fwdDiff (1 : ℕ))^[k] (fun n : ℕ => (n : ℝ) ^ t)) 0 =
    (Nat.stirlingSecond t k : ℝ) * (k.factorial : ℝ) := by
  have hfun : (fun n : ℕ => (n : ℝ) ^ t) =
    ∑ l ∈ Finset.range (t + 1),
      ((Nat.stirlingSecond t l : ℝ) * (l.factorial : ℝ)) •
        (fun n : ℕ => (Nat.choose n l : ℝ)) := by
    funext n
    rw [pow_eq_sum_stirlingSecond_mul_factorial_choose]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, fwdDiff_iter_finsetSum]
  simp only [fwdDiff_iter_const_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    fwdDiff_iter_choose_zero]
  by_cases hk : k ∈ Finset.range (t + 1)
  · rw [Finset.sum_eq_single k]
    · simp
    · intro l hl hlk
      simp [Ne.symm hlk]
    · exact fun h => (h hk).elim
  · have htk : t < k := by
    simp only [Finset.mem_range, not_lt] at hk
    omega
    rw [Nat.stirlingSecond_eq_zero_of_lt htk, Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro l hl
    have hkl : k ≠ l := by
      intro h
      subst h
      exact hk hl
    simp [hkl]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[stirlingSecond_mul_factorial_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
lemma stirlingSecond_mul_factorial_eq_sum
  {t k : ℕ} :
-- imply
  (Nat.stirlingSecond t k : ℝ) * (k.factorial : ℝ) =
    ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ (k - j) * (Nat.choose k j : ℝ) * (j : ℝ) ^ t := by
-- proof
  rw [← fwdDiff_iter_pow_zero t k]
  rw [fwdDiff_iter_eq_sum_shift]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[choose_succ_absorb_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
private lemma choose_succ_absorb_real (a b : ℕ) :
  (Nat.choose (a + 1) (b + 1) : ℝ) * ((b : ℝ) + 1) =
    ((a : ℝ) + 1) * (Nat.choose a b : ℝ) := by
  exact_mod_cast (Nat.add_one_mul_choose_eq a b).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[stirlingSecond_succ_mul_factorial_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
private lemma stirlingSecond_succ_mul_factorial_eq_sum (n j : ℕ) :
  (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) * (j.factorial : ℝ) =
    ∑ i ∈ Finset.range (j + 1),
      (-1 : ℝ) ^ (j - i) * (Nat.choose j i : ℝ) * ((i : ℝ) + 1) ^ n := by
  have h := stirlingSecond_mul_factorial_eq_sum (n + 1) (j + 1)
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero n), mul_zero, add_zero] at h
  have hsum :
    (∑ i ∈ Finset.range (j + 1),
      (-1 : ℝ) ^ (j + 1 - (i + 1)) * (Nat.choose (j + 1) (i + 1) : ℝ) *
        ((i + 1 : ℕ) : ℝ) ^ (n + 1)) =
      ((j : ℝ) + 1) * ∑ i ∈ Finset.range (j + 1),
        (-1 : ℝ) ^ (j - i) * (Nat.choose j i : ℝ) * ((i : ℝ) + 1) ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have habs := choose_succ_absorb_real j i
    have hsub : j + 1 - (i + 1) = j - i := by omega
    rw [hsub, pow_succ]
    push_cast
    linear_combination (-1 : ℝ) ^ (j - i) * ((i : ℝ) + 1) ^ n * habs
  rw [hsum] at h
  have hfact : (Nat.factorial (j + 1) : ℝ) =
    ((j : ℝ) + 1) * (Nat.factorial j : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfact] at h
  apply mul_left_cancel₀ (show (j : ℝ) + 1 ≠ 0 by positivity)
  calc
    ((j : ℝ) + 1) *
      ((Nat.stirlingSecond (n + 1) (j + 1) : ℝ) * (Nat.factorial j : ℝ)) =
      (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
        (((j : ℝ) + 1) * (Nat.factorial j : ℝ)) := by ring
    _ = ((j : ℝ) + 1) * ∑ i ∈ Finset.range (j + 1),
      (-1 : ℝ) ^ (j - i) * (Nat.choose j i : ℝ) * ((i : ℝ) + 1) ^ n := h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hasSum_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
private lemma hasSum_exp (x : ℝ) :
  HasSum (fun n : ℕ => x ^ n / n.factorial) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact (Real.summable_pow_div_factorial x).hasSum

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hasSum_finset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
private lemma hasSum_finset {ι : Type*} (s : Finset ι)
  (f : ι → ℕ → ℝ) (g : ι → ℝ) (h : ∀ i ∈ s, HasSum (f i) (g i)) :
  HasSum (fun n => ∑ i ∈ s, f i n) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hasSum_zero
  | @insert a s ha ih =>
    simpa [Finset.sum_insert ha] using (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[binomial_exp_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
private lemma binomial_exp_sum (j : ℕ) (x : ℝ) :
  ∑ i ∈ Finset.range (j + 1),
    (-1 : ℝ) ^ (j - i) * (Nat.choose j i : ℝ) * Real.exp (((i : ℝ) + 1) * x) =
    Real.exp x * (Real.exp x - 1) ^ j := by
  calc
    (∑ i ∈ Finset.range (j + 1),
      (-1 : ℝ) ^ (j - i) * (Nat.choose j i : ℝ) * Real.exp (((i : ℝ) + 1) * x)) =
      Real.exp x * ∑ i ∈ Finset.range (j + 1),
        (-1 : ℝ) ^ (j - i) * (Nat.choose j i : ℝ) * Real.exp x ^ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [show ((i : ℝ) + 1) * x = x + (i : ℝ) * x by ring,
            Real.exp_add, Real.exp_nat_mul]
          ring
    _ = Real.exp x * (Real.exp x - 1) ^ j := by
      congr 1
      rw [show Real.exp x - 1 = (-1 : ℝ) + Real.exp x by ring,
        add_comm (-1 : ℝ) (Real.exp x), add_pow]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hasSum_stirlingSecond_succ_egf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
lemma hasSum_stirlingSecond_succ_egf
  {j : ℕ}
  {x : ℝ} :
-- imply
  HasSum
    (fun n : ℕ =>
    (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) * (x ^ n / n.factorial))
    (Real.exp x * (Real.exp x - 1) ^ j / j.factorial) := by
-- proof
  let c : ℕ → ℝ := fun i =>
    (-1 : ℝ) ^ (j - i) * (Nat.choose j i : ℝ)
  let a : ℕ → ℝ := fun i => (i : ℝ) + 1
  have hs : HasSum
    (fun n : ℕ => ∑ i ∈ Finset.range (j + 1),
      (c i / (j.factorial : ℝ)) * ((a i * x) ^ n / n.factorial))
    (∑ i ∈ Finset.range (j + 1),
      (c i / (j.factorial : ℝ)) * Real.exp (a i * x)) := by
    apply hasSum_finset
    intro i hi
    exact (hasSum_exp (a i * x)).mul_left (c i / (j.factorial : ℝ))
  have hterm : ∀ n : ℕ,
    (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) * (x ^ n / n.factorial) =
      ∑ i ∈ Finset.range (j + 1),
        (c i / (j.factorial : ℝ)) * ((a i * x) ^ n / n.factorial) := by
    intro n
    have hstir := stirlingSecond_succ_mul_factorial_eq_sum n j
    have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
    symm
    calc
      (∑ i ∈ Finset.range (j + 1),
        (c i / (j.factorial : ℝ)) * ((a i * x) ^ n / n.factorial)) =
        (∑ i ∈ Finset.range (j + 1), c i * a i ^ n) *
          (x ^ n / ((j.factorial : ℝ) * (n.factorial : ℝ))) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            rw [mul_pow]
            ring
      _ = ((Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
        (j.factorial : ℝ)) *
          (x ^ n / ((j.factorial : ℝ) * (n.factorial : ℝ))) := by
            rw [hstir]
      _ = (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
        (x ^ n / n.factorial) := by
          field_simp [hfac]
  have hlimit :
    (∑ i ∈ Finset.range (j + 1),
      (c i / (j.factorial : ℝ)) * Real.exp (a i * x)) =
      Real.exp x * (Real.exp x - 1) ^ j / j.factorial := by
    calc
      (∑ i ∈ Finset.range (j + 1),
        (c i / (j.factorial : ℝ)) * Real.exp (a i * x)) =
        (∑ i ∈ Finset.range (j + 1), c i * Real.exp (a i * x)) /
          (j.factorial : ℝ) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = Real.exp x * (Real.exp x - 1) ^ j / j.factorial := by
        rw [binomial_exp_sum]
  rw [← hlimit]
  exact hs.congr_fun hterm

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
