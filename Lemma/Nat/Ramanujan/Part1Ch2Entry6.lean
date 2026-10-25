import Mathlib
import sympy.Basic
import Def.NumberTheory.Ramanujan.Part1Ch2Entry6
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry6


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[A_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
lemma A_zero
  {n : ℕ} :
-- imply
  A n 0 = n := by
-- proof
simp [A]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[A_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
lemma A_succ
  {n k : ℕ} :
-- imply
  A n (k + 1) = 3 * A n k + 1 := by
-- proof
  unfold A
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  have h3k : 3 ^ k = 2 * m + 1 := by omega
  rw [pow_succ, h3k]
  have h1 : (2 * m + 1 - 1) / 2 = m := by omega
  have h2 : ((2 * m + 1) * 3 - 1) / 2 = 3 * m + 1 := by omega
  rw [h1, h2]
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[A_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
lemma A_ge
  {n k : ℕ} :
-- imply
  n ≤ A n k := by
-- proof
  induction k with
  | zero => rw [A_zero]
  | succ k ih => rw [A_succ]; omega

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[sum_Icc_split](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma sum_Icc_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b c : ℕ)
  (hab : a ≤ b + 1) (hbc : b ≤ c) :
  ∑ k ∈ Finset.Icc a c, f k =
    ∑ k ∈ Finset.Icc a b, f k + ∑ k ∈ Finset.Icc (b + 1) c, f k := by
  induction c, hbc using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega : ¬ (b + 1 ≤ b))]
    simp
  | succ n hbn ih =>
    have h1 : a ≤ n + 1 := by omega
    have h2 : b + 1 ≤ n + 1 := by omega
    rw [Finset.sum_Icc_succ_top h1 f, Finset.sum_Icc_succ_top h2 f, ih]
    abel

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[triple_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma triple_sum (f : ℕ → ℚ) (L : ℕ) (hL : 1 ≤ L) (U : ℕ) :
  ∑ j ∈ Finset.Icc L U, (f (3 * j - 1) + f (3 * j) + f (3 * j + 1)) =
  ∑ m ∈ Finset.Icc (3 * L - 1) (3 * U + 1), f m := by
  induction U with
  | zero =>
    have e1 : Finset.Icc L 0 = ∅ := Finset.Icc_eq_empty (by omega)
    have e2 : Finset.Icc (3 * L - 1) (3 * 0 + 1) = ∅ := by
      apply Finset.Icc_eq_empty
      omega
    rw [e1, e2, Finset.sum_empty, Finset.sum_empty]
  | succ U ih =>
    by_cases h : L ≤ U + 1
    · have hLU : L ≤ U ∨ L = U + 1 := by omega
      obtain hLU | hLU := hLU
      · rw [Finset.sum_Icc_succ_top h (fun j => f (3 * j - 1) + f (3 * j) + f (3 * j + 1))]
        have hsplit : ∑ m ∈ Finset.Icc (3 * L - 1) (3 * (U + 1) + 1), f m =
          ∑ m ∈ Finset.Icc (3 * L - 1) (3 * U + 1), f m +
          (f (3 * U + 2) + f (3 * U + 3) + f (3 * U + 4)) := by
          have e1 : 3 * (U + 1) + 1 = (3 * U + 1) + 3 := by ring
          rw [e1]
          have s1 : ∑ m ∈ Finset.Icc (3 * L - 1) ((3 * U + 1) + 3), f m =
            ∑ m ∈ Finset.Icc (3 * L - 1) ((3 * U + 1) + 2), f m + f ((3 * U + 1) + 3) := by
            apply Finset.sum_Icc_succ_top
            omega
          have s2 : ∑ m ∈ Finset.Icc (3 * L - 1) ((3 * U + 1) + 2), f m =
            ∑ m ∈ Finset.Icc (3 * L - 1) ((3 * U + 1) + 1), f m + f ((3 * U + 1) + 2) := by
            apply Finset.sum_Icc_succ_top
            omega
          have s3 : ∑ m ∈ Finset.Icc (3 * L - 1) ((3 * U + 1) + 1), f m =
            ∑ m ∈ Finset.Icc (3 * L - 1) (3 * U + 1), f m + f ((3 * U + 1) + 1) := by
            apply Finset.sum_Icc_succ_top
            omega
          rw [s1, s2, s3]
          have e2 : (3 * U + 1) + 1 = 3 * U + 2 := by ring
          have e3 : (3 * U + 1) + 2 = 3 * U + 3 := by ring
          have e4 : (3 * U + 1) + 3 = 3 * U + 4 := by ring
          have q2 : f ((3 * U + 1) + 1) = f (3 * U + 2) := congrArg f e2
          have q3 : f ((3 * U + 1) + 2) = f (3 * U + 3) := congrArg f e3
          have q4 : f ((3 * U + 1) + 3) = f (3 * U + 4) := congrArg f e4
          rw [q2, q3, q4]
          abel
        rw [hsplit, ih]
        have g1 : 3 * (U + 1) - 1 = 3 * U + 2 := by omega
        have g2 : 3 * (U + 1) = 3 * U + 3 := by ring
        have g3 : 3 * (U + 1) + 1 = 3 * U + 4 := by ring
        have e1 : f (3 * (U + 1) - 1) = f (3 * U + 2) := congrArg f g1
        have e2 : f (3 * (U + 1)) = f (3 * U + 3) := congrArg f g2
        have e3 : f (3 * (U + 1) + 1) = f (3 * U + 4) := congrArg f g3
        rw [e1, e2, e3]
      · subst hLU
        rw [Finset.sum_Icc_succ_top h (fun j => f (3 * j - 1) + f (3 * j) + f (3 * j + 1))]
        have e0 : Finset.Icc (U + 1) U = ∅ := Finset.Icc_eq_empty (by omega)
        rw [e0, Finset.sum_empty]
        simp only [zero_add]
        have g1 : 3 * (U + 1) - 1 = 3 * U + 2 := by omega
        have g2 : 3 * (U + 1) = 3 * U + 3 := by ring
        have g3 : 3 * (U + 1) + 1 = 3 * U + 4 := by ring
        have e1 : f (3 * (U + 1) - 1) = f (3 * U + 2) := congrArg f g1
        have e2 : f (3 * (U + 1)) = f (3 * U + 3) := congrArg f g2
        have e3 : f (3 * (U + 1) + 1) = f (3 * U + 4) := congrArg f g3
        rw [e1, e2, e3]
        have eR : 3 * (U + 1) - 1 = 3 * U + 2 := by omega
        have eR2 : 3 * (U + 1) + 1 = 3 * U + 4 := by ring
        rw [eR, eR2]
        have s1 : ∑ m ∈ Finset.Icc (3 * U + 2) (3 * U + 4), f m =
          ∑ m ∈ Finset.Icc (3 * U + 2) (3 * U + 3), f m + f (3 * U + 4) :=
          Finset.sum_Icc_succ_top (by omega) f
        have s2 : ∑ m ∈ Finset.Icc (3 * U + 2) (3 * U + 3), f m =
          ∑ m ∈ Finset.Icc (3 * U + 2) (3 * U + 2), f m + f (3 * U + 3) :=
          Finset.sum_Icc_succ_top (by omega) f
        rw [s1, s2]
        simp
    · have eL : Finset.Icc L (U + 1) = ∅ := Finset.Icc_eq_empty (by omega)
      have hU : ¬ L ≤ U := by omega
      rw [eL]
      have eR : Finset.Icc (3 * L - 1) (3 * (U + 1) + 1) = ∅ := by
        apply Finset.Icc_eq_empty
        omega
      rw [eR, Finset.sum_empty, Finset.sum_empty]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[key_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma key_general (x : ℚ) (hx : x ≠ 0) (hx1 : x - 1 ≠ 0) (hx2 : x + 1 ≠ 0)
  (hx4 : x ^ 2 - 1 ≠ 0) :
  1 / (x - 1) + 1 / x + 1 / (x + 1) = 3 / x + 2 / (x ^ 3 - x) := by
  field_simp
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[key_nat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma key_nat (j : ℕ) (hj : 1 ≤ j) :
  (1 : ℚ) / (((3 * j - 1 : ℕ)) : ℚ) + (1 : ℚ) / (((3 * j : ℕ)) : ℚ)
    + (1 : ℚ) / (((3 * j + 1 : ℕ)) : ℚ)
  = (1 : ℚ) / ((j : ℕ) : ℚ) + 2 * ((1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))) := by
  have hjQ : ((j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (by omega : 0 < j)
  have hj1Q : (1 : ℚ) ≤ ((j : ℕ) : ℚ) := by exact_mod_cast hj
  have h1 : (1 : ℕ) ≤ 3 * j := by omega
  have c1 : (((3 * j - 1 : ℕ)) : ℚ) = 3 * ((j : ℕ) : ℚ) - 1 := by
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have c2 : (((3 * j : ℕ)) : ℚ) = 3 * ((j : ℕ) : ℚ) := by push_cast; ring
  have c3 : (((3 * j + 1 : ℕ)) : ℚ) = 3 * ((j : ℕ) : ℚ) + 1 := by push_cast; ring
  rw [c1, c2, c3]
  have hx : (3 : ℚ) * ((j : ℕ) : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hjQ
  have hx1 : (3 : ℚ) * ((j : ℕ) : ℚ) - 1 ≠ 0 := by
    have h3 : (3 : ℚ) ≤ 3 * ((j : ℕ) : ℚ) := by linarith
    intro hcon
    linarith
  have hx2 : (3 : ℚ) * ((j : ℕ) : ℚ) + 1 ≠ 0 := by
    have h3 : (0 : ℚ) < 3 * ((j : ℕ) : ℚ) + 1 := by positivity
    exact ne_of_gt h3
  have hx4 : ((3 : ℚ) * ((j : ℕ) : ℚ)) ^ 2 - 1 ≠ 0 := by
    have hsq : (1 : ℚ) < ((3 : ℚ) * ((j : ℕ) : ℚ)) ^ 2 := by nlinarith
    intro hcon
    linarith
  have key := key_general (3 * ((j : ℕ) : ℚ)) hx hx1 hx2 hx4
  have h3j : (3 : ℚ) / (3 * ((j : ℕ) : ℚ)) = (1 : ℚ) / ((j : ℕ) : ℚ) := by
    field_simp
  have hD : ((3 : ℚ) * ((j : ℕ) : ℚ)) ^ 3 - (3 : ℚ) * ((j : ℕ) : ℚ)
    = (3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ) := by ring
  rw [hD] at key
  have h2 : (2 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))
    = 2 * ((1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))) := by ring
  rwa [h3j, h2] at key

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[H1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma H1 (n : ℕ) :
  ∑ m ∈ Finset.Icc (n + 1) (A n 1), (1 : ℚ) / ((m : ℕ) : ℚ)
  = 1 + 2 * ∑ j ∈ Finset.Icc 1 (A n 0),
    (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
  have eA0 : A n 0 = n := A_zero n
  have eA1 : A n 1 = 3 * n + 1 := by
    have h := A_succ n 0
    rw [eA0] at h
    simpa using h
  rw [eA0, eA1]
  have htriple := triple_sum (fun m => (1 : ℚ) / ((m : ℕ) : ℚ)) 1 (le_refl 1) n
  simp only [mul_one] at htriple
  have hrewrite : ∑ j ∈ Finset.Icc 1 n,
    ((1 : ℚ) / (((3 * j - 1 : ℕ)) : ℚ) + (1 : ℚ) / (((3 * j : ℕ)) : ℚ)
      + (1 : ℚ) / (((3 * j + 1 : ℕ)) : ℚ))
    = ∑ j ∈ Finset.Icc 1 n, (1 : ℚ) / ((j : ℕ) : ℚ)
      + 2 * ∑ j ∈ Finset.Icc 1 n, (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
    have hcongr : ∀ j ∈ Finset.Icc 1 n,
      ((1 : ℚ) / (((3 * j - 1 : ℕ)) : ℚ) + (1 : ℚ) / (((3 * j : ℕ)) : ℚ)
        + (1 : ℚ) / (((3 * j + 1 : ℕ)) : ℚ))
      = ((1 : ℚ) / ((j : ℕ) : ℚ)
        + 2 * ((1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)))) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      exact key_nat j hj.1
    rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hLHS : ∑ j ∈ Finset.Icc 1 n,
    ((fun m => (1 : ℚ) / ((m : ℕ) : ℚ)) (3 * j - 1)
      + (fun m => (1 : ℚ) / ((m : ℕ) : ℚ)) (3 * j)
      + (fun m => (1 : ℚ) / ((m : ℕ) : ℚ)) (3 * j + 1))
    = ∑ j ∈ Finset.Icc 1 n,
      ((1 : ℚ) / (((3 * j - 1 : ℕ)) : ℚ) + (1 : ℚ) / (((3 * j : ℕ)) : ℚ)
        + (1 : ℚ) / (((3 * j + 1 : ℕ)) : ℚ)) := by
    rfl
  rw [hLHS, hrewrite] at htriple
  have hRHS : Finset.Icc (3 * 1 - 1) (3 * n + 1) = Finset.Icc 2 (3 * n + 1) := by norm_num
  rw [hRHS] at htriple
  have hsplit1 : ∑ m ∈ Finset.Icc 1 (3 * n + 1), (1 : ℚ) / ((m : ℕ) : ℚ)
    = ∑ m ∈ Finset.Icc 1 n, (1 : ℚ) / ((m : ℕ) : ℚ)
      + ∑ m ∈ Finset.Icc (n + 1) (3 * n + 1), (1 : ℚ) / ((m : ℕ) : ℚ) :=
    sum_Icc_split _ 1 n (3 * n + 1) (by omega) (by omega)
  have hsplit2 : ∑ m ∈ Finset.Icc 1 (3 * n + 1), (1 : ℚ) / ((m : ℕ) : ℚ)
    = ∑ m ∈ Finset.Icc 1 1, (1 : ℚ) / ((m : ℕ) : ℚ)
      + ∑ m ∈ Finset.Icc (1 + 1) (3 * n + 1), (1 : ℚ) / ((m : ℕ) : ℚ) :=
    sum_Icc_split (fun m => (1 : ℚ) / ((m : ℕ) : ℚ)) 1 1 (3 * n + 1) (by omega) (by omega)
  have h11 : ∑ m ∈ Finset.Icc 1 1, (1 : ℚ) / ((m : ℕ) : ℚ) = 1 := by simp
  have h22 : Finset.Icc (1 + 1) (3 * n + 1) = Finset.Icc 2 (3 * n + 1) := by norm_num
  rw [h11, h22] at hsplit2
  linarith

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[Hstep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma Hstep (n k : ℕ) (hk : 1 ≤ k) :
  ∑ m ∈ Finset.Icc (A n k + 1) (A n (k + 1)), (1 : ℚ) / ((m : ℕ) : ℚ)
  = ∑ j ∈ Finset.Icc (A n (k - 1) + 1) (A n k), (1 : ℚ) / ((j : ℕ) : ℚ)
    + 2 * ∑ j ∈ Finset.Icc (A n (k - 1) + 1) (A n k),
      (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
  have hkk : k - 1 + 1 = k := by omega
  have hAkm : A n k = 3 * A n (k - 1) + 1 := by
    have h := A_succ n (k - 1)
    rwa [hkk] at h
  have hL : 1 ≤ A n (k - 1) + 1 := by omega
  have htriple := triple_sum (fun m => (1 : ℚ) / ((m : ℕ) : ℚ)) (A n (k - 1) + 1) hL (A n k)
  have eLow : 3 * (A n (k - 1) + 1) - 1 = A n k + 1 := by omega
  have eUp : 3 * A n k + 1 = A n (k + 1) := by
    have h := A_succ n k
    omega
  rw [eLow, eUp] at htriple
  have hrewrite : ∑ j ∈ Finset.Icc (A n (k - 1) + 1) (A n k),
    ((1 : ℚ) / (((3 * j - 1 : ℕ)) : ℚ) + (1 : ℚ) / (((3 * j : ℕ)) : ℚ)
      + (1 : ℚ) / (((3 * j + 1 : ℕ)) : ℚ))
    = ∑ j ∈ Finset.Icc (A n (k - 1) + 1) (A n k), (1 : ℚ) / ((j : ℕ) : ℚ)
      + 2 * ∑ j ∈ Finset.Icc (A n (k - 1) + 1) (A n k),
        (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
    have hcongr : ∀ j ∈ Finset.Icc (A n (k - 1) + 1) (A n k),
      ((1 : ℚ) / (((3 * j - 1 : ℕ)) : ℚ) + (1 : ℚ) / (((3 * j : ℕ)) : ℚ)
        + (1 : ℚ) / (((3 * j + 1 : ℕ)) : ℚ))
      = ((1 : ℚ) / ((j : ℕ) : ℚ)
        + 2 * ((1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)))) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      have hj1 : 1 ≤ j := by omega
      exact key_nat j hj1
    rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hLHS : ∑ j ∈ Finset.Icc (A n (k - 1) + 1) (A n k),
    ((fun m => (1 : ℚ) / ((m : ℕ) : ℚ)) (3 * j - 1)
      + (fun m => (1 : ℚ) / ((m : ℕ) : ℚ)) (3 * j)
      + (fun m => (1 : ℚ) / ((m : ℕ) : ℚ)) (3 * j + 1))
    = ∑ j ∈ Finset.Icc (A n (k - 1) + 1) (A n k),
      ((1 : ℚ) / (((3 * j - 1 : ℕ)) : ℚ) + (1 : ℚ) / (((3 * j : ℕ)) : ℚ)
        + (1 : ℚ) / (((3 * j + 1 : ℕ)) : ℚ)) := by
    rfl
  rwa [hLHS, hrewrite] at htriple

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma aux (n m : ℕ) :
  ∑ j ∈ Finset.Icc (A n m + 1) (A n (m + 1)), (1 : ℚ) / ((j : ℕ) : ℚ)
  = 1 + 2 * ∑ k ∈ Finset.range (m + 1),
    ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
      (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
  induction m with
  | zero =>
    have hH1 := H1 n
    have eA0 : A n 0 = n := A_zero n
    have hrange : ∑ k ∈ Finset.range 1,
      ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
        (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))
      = ∑ j ∈ Finset.Icc 1 (A n 0),
        (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
      simp
    rw [hrange, eA0]
    have e01 : A n (0 + 1) = A n 1 := by norm_num
    rw [e01]
    rwa [eA0] at hH1
  | succ m ih =>
    have hstep := Hstep n (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
    have hmsub : m + 1 - 1 = m := by omega
    rw [hmsub] at hstep
    have hrange : ∑ k ∈ Finset.range (m + 1 + 1),
      ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
        (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))
      = ∑ k ∈ Finset.range (m + 1),
        ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
          (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))
        + ∑ j ∈ Finset.Icc (A n m + 1) (A n (m + 1)),
          (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
      rw [Finset.sum_range_succ]
      congr 1
    rw [hrange]
    linarith

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[ramanujan_part1_ch2_entry6_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry6_general
  {n r : ℕ} :
-- imply
  ∑ j ∈ Finset.Icc (n + 1) (A n r), (1 : ℚ) / ((j : ℕ) : ℚ)
    = (r : ℚ) + 2 * ∑ k ∈ Finset.range r, (((r - k : ℕ)) : ℚ) *
    ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
    (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
-- proof
  induction r with
  | zero =>
    have eA0 : A n 0 = n := A_zero n
    rw [eA0]
    have eempty : Finset.Icc (n + 1) n = ∅ := Finset.Icc_eq_empty (by omega)
    rw [eempty, Finset.sum_empty, Finset.range_zero, Finset.sum_empty]
    simp
  | succ r ih =>
    have hAge : n ≤ A n r := A_ge n r
    have hAle : A n r ≤ A n (r + 1) := by
      have h := A_succ n r
      omega
    have hLHS : ∑ j ∈ Finset.Icc (n + 1) (A n (r + 1)), (1 : ℚ) / ((j : ℕ) : ℚ)
      = ∑ j ∈ Finset.Icc (n + 1) (A n r), (1 : ℚ) / ((j : ℕ) : ℚ)
        + ∑ j ∈ Finset.Icc (A n r + 1) (A n (r + 1)), (1 : ℚ) / ((j : ℕ) : ℚ) :=
      sum_Icc_split _ (n + 1) (A n r) (A n (r + 1)) (by omega) hAle
    have haux := aux n r
    -- RHS weight manipulation: prove weight identity first
    have hweight : ∑ k ∈ Finset.range (r + 1), (((r + 1 - k : ℕ)) : ℚ) *
      ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
        (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))
      = ∑ k ∈ Finset.range r, (((r - k : ℕ)) : ℚ) *
        ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
          (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))
        + ∑ k ∈ Finset.range (r + 1),
        ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
          (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
      have h1 : ∀ k ∈ Finset.range (r + 1), (((r + 1 - k : ℕ)) : ℚ) *
        ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
          (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))
        = ((((r - k : ℕ)) : ℚ) *
          ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
            (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))
          + ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
            (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))) := by
        intro k hk
        simp only [Finset.mem_range] at hk
        have hNat : r + 1 - k = (r - k) + 1 := by omega
        have hcast : (((r + 1 - k : ℕ)) : ℚ) = (((r - k : ℕ)) : ℚ) + 1 := by
          rw [hNat]
          push_cast
          ring
        rw [hcast]
        ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      congr 1
      have hlast : (((r - r : ℕ)) : ℚ) *
        ∑ j ∈ Finset.Icc (if r = 0 then 1 else A n (r - 1) + 1) (A n r),
          (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) = 0 := by
        simp
      have hsplit : ∑ k ∈ Finset.range (r + 1), (((r - k : ℕ)) : ℚ) *
        ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
          (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))
        = ∑ k ∈ Finset.range r, (((r - k : ℕ)) : ℚ) *
          ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
            (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
        rw [Finset.sum_range_succ]
        rw [hlast, add_zero]
      exact hsplit
    have hcastR : (((r + 1 : ℕ)) : ℚ) = (r : ℚ) + 1 := by push_cast; ring
    rw [hLHS, ih, haux]
    have hgoal : (r : ℚ) + 2 * ∑ k ∈ Finset.range r, (((r - k : ℕ)) : ℚ) *
      ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
        (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ))
      + (1 + 2 * ∑ k ∈ Finset.range (r + 1),
        ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
          (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)))
      = (((r + 1 : ℕ)) : ℚ) + 2 * ∑ k ∈ Finset.range (r + 1), (((r + 1 - k : ℕ)) : ℚ) *
        ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
          (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
      rw [hweight, hcastR]
      ring
    linarith [hgoal]
set_option linter.unusedVariables false in

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

/--
[ramanujan_part1_ch2_entry6](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry6
  {n r : ℕ}
-- given
  (hr : 0 < r) :
-- imply
  ∑ j ∈ Finset.Icc (n + 1) (A n r), (1 : ℚ) / (j : ℚ) =
    (r : ℚ) + 2 * ∑ k ∈ Finset.range r, ((r - k : ℕ) : ℚ) *
    ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k), (1 : ℚ) /
    ((3 * (j : ℚ)) ^ 3 - 3 * (j : ℚ)) :=
-- proof
  ramanujan_part1_ch2_entry6_general n r

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6


-- created on 2026-10-20
-- updated on 2026-10-23
