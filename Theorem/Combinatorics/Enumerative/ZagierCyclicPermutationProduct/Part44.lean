/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part44
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagCyclePairs_card_eq_zero_of_lt (n k : ℕ) (hnk : n < k) :
    Nat.card (ZagCyclePairs n k) = 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  constructor
  intro p
  have hle := zagCycleQuotientCount_le (p.1.1 * p.1.2)
  rw [p.2.2.2] at hle
  omega

theorem zagCyclePairs_cross_mul_gap
    (n r : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (hgap : n - k = 2 * r) :
    (n + 1).choose 2 * Nat.card (ZagCyclePairs n k) =
      (n - 1).factorial * Nat.stirlingFirst (n + 1) k := by
  induction r using Nat.strong_induction_on generalizing k with
  | h r ih =>
      have hparity : Even (n - k) := ⟨r, by omega⟩
      have hpairs := zagCyclePairs_recurrence n k hn hk hkn hparity
      have hstirling := zagStirlingFirst_recurrence n k hn hk hkn
      let C := (n + 1).choose 2
      let F := (n - 1).factorial
      let pairSum := ∑ d : Fin n,
        (k + 2 * (d.val + 1)).choose (k - 1) *
          Nat.card (ZagCyclePairs n (k + 2 * (d.val + 1)))
      let stirlingSum := ∑ d : Fin n,
        (k + 2 * (d.val + 1)).choose (k - 1) *
          Nat.stirlingFirst (n + 1) (k + 2 * (d.val + 1))
      have hsum : C * pairSum = F * stirlingSum := by
        dsimp only [pairSum, stirlingSum]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        let j := k + 2 * (d.val + 1)
        by_cases hjn : j ≤ n
        · have hjk : k < j := by dsimp only [j]; omega
          have hjgap : n - j = 2 * (r - (d.val + 1)) := by
            dsimp only [j]
            omega
          have hjr : r - (d.val + 1) < r := by omega
          have hjformula := ih (r - (d.val + 1)) hjr j (by omega) hjn hjgap
          dsimp only [C, F]
          dsimp only [j] at hjformula
          nlinarith
        · have hnj : n + 1 < j := by
            dsimp only [j]
            omega
          rw [zagCyclePairs_card_eq_zero_of_lt n j (by omega),
            Nat.stirlingFirst_eq_zero_of_lt hnj]
          simp
      dsimp only [C, F, pairSum, stirlingSum] at hsum
      apply Nat.mul_left_cancel (by omega : 0 < n + 1 - k)
      nlinarith

theorem zagCyclePairs_cross_mul
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (hparity : Even (n - k)) :
    (n + 1).choose 2 * Nat.card (ZagCyclePairs n k) =
      (n - 1).factorial * Nat.stirlingFirst (n + 1) k := by
  obtain ⟨r, hr⟩ := hparity
  apply zagCyclePairs_cross_mul_gap n r hn k hk hkn
  omega

/--
Zagier's formula for the probability that the product of two uniformly chosen cyclic
permutations of `Fin n` has exactly `k` cycles:
`(1 + (-1) ^ (n - k)) / Nat.factorial (n + 1) * Nat.stirlingFirst (n + 1) k`.
Cyclicity is encoded as cycle-type-plus-fixed-points count equal to one.

Source: R. Cori and G. Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem [Zagier], lines 351-359,
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Hetyei/hetyei2.tex>, quoting D. Zagier.

Proof: We formalize the plane-permutation transposition and reflection bijections of
Chen and Reidys, arXiv:1502.07674, lines 786-1074, and their specialization to Zagier's
recurrence, lines 1167-1370. A generating-polynomial coefficient identity supplies the
matching Stirling recurrence; descending induction on the cycle count finishes.

Proves `Wanted` entry `zagier_probability_product_two_cyclic_permutations`.
-/
theorem zagier_probability_product_two_cyclic_permutations
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) :
    ((Fintype.card {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
        Multiset.card p.1.cycleType + Fintype.card (Function.fixedPoints p.1) = 1 ∧
        Multiset.card p.2.cycleType + Fintype.card (Function.fixedPoints p.2) = 1 ∧
        Multiset.card (p.1 * p.2).cycleType +
            Fintype.card (Function.fixedPoints (p.1 * p.2)) = k}) : ℚ) /
      ((Fintype.card {σ : Equiv.Perm (Fin n) //
          Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 1}) : ℚ) ^ 2 =
      (1 + (-1 : ℚ) ^ (n - k)) / Nat.factorial (n + 1) *
        Nat.stirlingFirst (n + 1) k := by
  have hnum :
      Fintype.card {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
          Multiset.card p.1.cycleType +
              Fintype.card (Function.fixedPoints p.1) = 1 ∧
          Multiset.card p.2.cycleType +
              Fintype.card (Function.fixedPoints p.2) = 1 ∧
          Multiset.card (p.1 * p.2).cycleType +
              Fintype.card (Function.fixedPoints (p.1 * p.2)) = k} =
        Nat.card (ZagCyclePairs n k) := by
    let E :
        {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) //
          Multiset.card p.1.cycleType +
              Fintype.card (Function.fixedPoints p.1) = 1 ∧
          Multiset.card p.2.cycleType +
              Fintype.card (Function.fixedPoints p.2) = 1 ∧
          Multiset.card (p.1 * p.2).cycleType +
              Fintype.card (Function.fixedPoints (p.1 * p.2)) = k} ≃
          ZagCyclePairs n k :=
      Equiv.subtypeEquivProp (funext fun p => propext (by
        simp only [cycleQuotientCount_eq]))
    calc
      _ = Fintype.card (ZagCyclePairs n k) := Fintype.card_congr E
      _ = Nat.card (ZagCyclePairs n k) := Nat.card_eq_fintype_card.symm
  rw [zagCard_fullCycles n hn]
  by_cases hparity : Even (n - k)
  · rw [hnum, hparity.neg_one_pow]
    norm_num
    have hcross := zagCyclePairs_cross_mul n k hn hk hkn hparity
    have hchoose := zagTwo_mul_choose_two (n + 1)
    rw [Nat.succ_sub_one] at hchoose
    have hfactorial :
        (n + 1).factorial = (n + 1) * n * (n - 1).factorial := by
      have hnEq : n - 1 + 1 = n := by omega
      rw [Nat.factorial_succ]
      conv_lhs =>
        enter [2]
        rw [show n = (n - 1) + 1 by omega, Nat.factorial_succ]
      rw [hnEq]
      simp only [mul_assoc]
    have hchooseQ :
        (2 : ℚ) * (n + 1).choose 2 = (n + 1) * n := by
      exact_mod_cast hchoose
    have hfactorialQ :
        ((n + 1).factorial : ℚ) = (n + 1) * n * (n - 1).factorial := by
      exact_mod_cast hfactorial
    have hcrossQ :
        ((n + 1).choose 2 : ℚ) * Nat.card (ZagCyclePairs n k) =
          (n - 1).factorial * Nat.stirlingFirst (n + 1) k := by
      exact_mod_cast hcross
    rw [Nat.card_eq_fintype_card] at hcrossQ
    have hsmallFactorial : ((n - 1).factorial : ℚ) ≠ 0 := by positivity
    have hlargeFactorial : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    calc
      (Fintype.card (ZagCyclePairs n k) : ℚ) * (n + 1).factorial =
          Fintype.card (ZagCyclePairs n k) *
            (((n + 1) * n) * (n - 1).factorial) := by rw [hfactorialQ]
      _ = Fintype.card (ZagCyclePairs n k) *
            ((2 * (n + 1).choose 2) * (n - 1).factorial) := by rw [hchooseQ]
      _ = 2 * ((n + 1).choose 2 * Fintype.card (ZagCyclePairs n k)) *
            (n - 1).factorial := by ring
      _ = 2 * ((n - 1).factorial * Nat.stirlingFirst (n + 1) k) *
            (n - 1).factorial := by rw [hcrossQ]
      _ = ((n - 1).factorial : ℚ) ^ 2 * 2 *
            Nat.stirlingFirst (n + 1) k := by ring
  · have hodd : Odd (n - k) := Nat.not_even_iff_odd.mp hparity
    rw [zagCard_cyclePairs_eq_zero_of_odd n k hodd, hodd.neg_one_pow]
    norm_num

end MetaMathlibExt
