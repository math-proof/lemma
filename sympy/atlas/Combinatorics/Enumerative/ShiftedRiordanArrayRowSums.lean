/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ShiftedRiordanArrayRowSums.lean -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Sum

namespace MetaMathlibExt

private theorem shiftedRiordan_aux_Icc_zero (n : ℕ) :
    Finset.Icc 0 n = Finset.range (n + 1) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_range]
  omega

private theorem shiftedRiordan_aux_binom {R : Type*} [CommSemiring R] (r : R) (j : ℕ) :
    (∑ k ∈ Finset.range (j + 1), (Nat.choose j k : R) * r ^ (j - k)) =
      (r + 1) ^ j := by
  have h := add_pow (1 : R) r j
  rw [add_comm (1 : R) r] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  rw [one_pow, one_mul]
  ring

/--
The constant term and coefficient sum of a shifted Riordan row polynomial: for
the `r`-shifted array, evaluating the row polynomial at 0 gives the column-0
entry `∑ k, A n k * r ^ k`, and evaluating at 1 (the row sum) gives the
column-0 entry of the `(r + 1)`-shifted array.

Source: José Agapito, Ângela Mestre, Maria M. Torres, and Pasquale Petrullo,
"On One-Parameter Catalan Arrays," Journal of Integer Sequences 18 (2015),
Article 15.5.1, Corollary (equations eqColumn0Rr and eqRowsumsRr),
lines 240–245, https://cs.uwaterloo.ca/journals/JIS/VOL18/Agapito/agapito2.tex

The `r`-Riordan array is Definition de1parameterRiordan (lines 220–222).
Proves `Wanted` entry `shiftedRiordanArray_constantTerm_and_sumCoefficients`.
-/
theorem shiftedRiordanArray_constantTerm_and_sumCoefficients
    {R : Type*} [CommSemiring R] (A : ℕ → ℕ → R) (r : R) (n : ℕ) :
    let shifted : R → ℕ → ℕ → R := fun s i j =>
      ∑ k ∈ Finset.Icc j i, (Nat.choose k j : R) * A i k * s ^ (k - j)
    let p : Polynomial R :=
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C (shifted r n k) * Polynomial.X ^ k
    Polynomial.eval 0 p = shifted r n 0 ∧
      shifted r n 0 = ∑ k ∈ Finset.range (n + 1), A n k * r ^ k ∧
      Polynomial.eval 1 p =
        ∑ k ∈ Finset.range (n + 1), shifted r n k ∧
      (∑ k ∈ Finset.range (n + 1), shifted r n k) =
        shifted (r + 1) n 0 := by
  intro shifted p
  have hIcc : Finset.Icc 0 n = Finset.range (n + 1) :=
    shiftedRiordan_aux_Icc_zero n
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    have h0mem : (0 : ℕ) ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.succ_pos n)
    have h := Finset.sum_eq_single_of_mem (0 : ℕ) h0mem (s := Finset.range (n + 1))
      (f := fun k => shifted r n k * (0 : R) ^ k)
      (fun k _ hne => by rw [zero_pow hne, mul_zero])
    simpa using h
  · simp only [shifted, hIcc]
    apply Finset.sum_congr rfl
    intro k _
    simp [Nat.choose_zero_right]
  · simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.sum_congr rfl
    intro k _
    simp
  · simp only [shifted, hIcc]
    have hRHS : (∑ k ∈ Finset.range (n + 1),
          (Nat.choose k 0 : R) * A n k * (r + 1) ^ (k - 0))
        = ∑ j ∈ Finset.range (n + 1), A n j * (r + 1) ^ j := by
      apply Finset.sum_congr rfl
      intro k _
      simp [Nat.choose_zero_right]
    rw [hRHS]
    have stepA : ∀ k ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.Icc k n, (Nat.choose j k : R) * A n j * r ^ (j - k))
        = ∑ j ∈ Finset.range (n + 1),
          (if k ≤ j then (Nat.choose j k : R) * A n j * r ^ (j - k) else 0) := by
      intro k _
      have hsub : Finset.Icc k n ⊆ Finset.range (n + 1) := by
        intro j hj
        simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
        omega
      have hcongr : (∑ j ∈ Finset.Icc k n,
            (Nat.choose j k : R) * A n j * r ^ (j - k))
          = ∑ j ∈ Finset.Icc k n,
            (if k ≤ j then (Nat.choose j k : R) * A n j * r ^ (j - k) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_Icc] at hj
        simp [hj.1]
      rw [hcongr]
      apply Finset.sum_subset hsub
      intro j hj1 hj2
      simp only [Finset.mem_range] at hj1
      simp only [Finset.mem_Icc] at hj2
      have hjle : j ≤ n := by omega
      have hnk : ¬ k ≤ j := fun h => hj2 ⟨h, hjle⟩
      simp [hnk]
    have eA : (∑ k ∈ Finset.range (n + 1),
          ∑ j ∈ Finset.Icc k n, (Nat.choose j k : R) * A n j * r ^ (j - k))
        = ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if k ≤ j then (Nat.choose j k : R) * A n j * r ^ (j - k) else 0) :=
      Finset.sum_congr rfl (fun k hk => stepA k hk)
    have eB : (∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if k ≤ j then (Nat.choose j k : R) * A n j * r ^ (j - k) else 0))
        = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (if k ≤ j then (Nat.choose j k : R) * A n j * r ^ (j - k) else 0) :=
      Finset.sum_comm
    have eC : (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (if k ≤ j then (Nat.choose j k : R) * A n j * r ^ (j - k) else 0))
        = ∑ j ∈ Finset.range (n + 1), A n j * (r + 1) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hsub2 : Finset.range (j + 1) ⊆ Finset.range (n + 1) := by
        intro k hk
        simp only [Finset.mem_range] at hk ⊢
        simp only [Finset.mem_range] at hj
        omega
      have e1 : (∑ k ∈ Finset.range (n + 1),
            (if k ≤ j then (Nat.choose j k : R) * A n j * r ^ (j - k) else 0))
          = ∑ k ∈ Finset.range (j + 1),
            (Nat.choose j k : R) * A n j * r ^ (j - k) := by
        have hcongr2 : (∑ k ∈ Finset.range (j + 1),
              (Nat.choose j k : R) * A n j * r ^ (j - k))
            = ∑ k ∈ Finset.range (j + 1),
              (if k ≤ j then (Nat.choose j k : R) * A n j * r ^ (j - k) else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_range] at hk
          have hkj : k ≤ j := by omega
          simp [hkj]
        rw [hcongr2]
        symm
        apply Finset.sum_subset hsub2
        intro k hk1 hk2
        simp only [Finset.mem_range] at hk1 hk2
        have hnk : ¬ k ≤ j := by omega
        simp [hnk]
      rw [e1]
      have e2 : (∑ k ∈ Finset.range (j + 1),
            (Nat.choose j k : R) * A n j * r ^ (j - k))
          = A n j * (∑ k ∈ Finset.range (j + 1),
            (Nat.choose j k : R) * r ^ (j - k)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [e2, shiftedRiordan_aux_binom r j]
    rw [eA, eB, eC]

end MetaMathlibExt
