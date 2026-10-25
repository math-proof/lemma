import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfProbability.code.BallotTheorem
open Classical in


/--
[ballotCount_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BallotTheorem.lean)
-/
@[path]
lemma ballotCount_zero_left
  {b : ℕ} :
-- imply
  ballotCount 0 b = 0 := by
-- proof
  simp [ballotCount]

/--
[ballotCount_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BallotTheorem.lean)
-/
@[path]
lemma ballotCount_succ_zero
  {a : ℕ} :
-- imply
  ballotCount (a + 1) 0 = 1 := by
-- proof
  simp [ballotCount]

/--
[ballotCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BallotTheorem.lean)
-/
@[path]
lemma ballotCount_le
  {a b : ℕ}
-- given
  (h : a ≤ b) :
-- imply
  ballotCount a b = 0 := by
-- proof
  cases a with
  | zero => simp
  | succ a =>
    cases b with
    | zero => omega
    | succ b => simp only [ballotCount]; rw [if_neg]; omega

/--
[ballot_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BallotTheorem.lean)
-/
@[path]
lemma ballot_theorem
  {a b : ℕ}
-- given
  (hab : a > b) :
-- imply
  ballotCount a b * (a + b) = (a - b) * Nat.choose (a + b) a := by
-- proof
  induction a, b using ballotCount.induct with
  | case1 b => omega
  | case2 a => simp [Nat.choose_self]
  | case3 a b hgt ih1 ih2 =>
    simp only [ballotCount, hgt, ↓reduceIte]
    by_cases hab2 : a > b + 1
    ·
      have ih_left := ih1 hab2
      have ih_right := ih2 (by omega : a + 1 > b)
      rw [show a + (b + 1) = a + 1 + b from by omega] at ih_left
      set n := a + 1 + b with hn_def
      rw [show a + 1 + (b + 1) = n + 1 from by omega]
      apply Nat.eq_of_mul_eq_mul_right (show 0 < n from by omega)
      apply Nat.eq_of_mul_eq_mul_right (show 0 < a + 1 from by omega)
      have ratio_nat : (b + 1) * Nat.choose n a = (a + 1) * Nat.choose n (a + 1) := by
        nlinarith [Nat.add_one_mul_choose_eq n a, Nat.choose_succ_succ n a]
      have succ_mul_nat := Nat.add_one_mul_choose_eq n a
      zify [show b + 1 ≤ a from by omega,
        show b ≤ a + 1 from by omega,
        show b + 1 ≤ a + 1 from by omega] at ih_left ih_right ratio_nat succ_mul_nat ⊢
      have hfn : (↑(ballotCount a (b + 1)) : ℤ) * ↑n * (↑a + 1) =
        (↑a - ↑b - 1) * ↑(Nat.choose n a) * (↑a + 1) := by
        linear_combination (↑a + 1) * ih_left
      have hgn : (↑(ballotCount (a + 1) b) : ℤ) * ↑n * (↑a + 1) =
        (↑a + 1 - ↑b) * (↑b + 1) * ↑(Nat.choose n a) := by
        linear_combination (↑a + 1) * ih_right - (↑a + 1 - ↑b) * ratio_nat
      have key : (↑(ballotCount a (b + 1)) + ↑(ballotCount (a + 1) b) : ℤ) * ↑n * (↑a + 1) =
        (↑a - ↑b) * ↑n * ↑(Nat.choose n a) := by
        have : (↑a - ↑b - 1) * ((↑a : ℤ) + 1) + (↑a + 1 - ↑b) * (↑b + 1) = (↑a - ↑b) * ↑n := by
          simp only [hn_def]; push_cast; ring
        nlinarith [hfn, hgn]
      linear_combination (↑n + 1) * key + (↑a - ↑b) * ↑n * succ_mul_nat
    ·
      have hab_eq : a = b + 1 := by omega
      subst hab_eq
      rw [ballotCount_le (le_refl _), zero_add]
      have ih := ih2 (by omega : b + 1 + 1 > b)
      have hih : ballotCount (b + 2) b * (2 * (b + 1)) =
        2 * Nat.choose (2 * (b + 1)) (b + 2) := by
        rw [show b + 1 + 1 + b = 2 * (b + 1) from by omega,
          show b + 1 + 1 - b = 2 from by omega] at ih
        linarith
      suffices ballotCount (b + 2) b * (2 * b + 3) = Nat.choose (2 * b + 3) (b + 2) by
        rw [show b + 1 + 1 + (b + 1) = 2 * b + 3 from by omega,
          show b + 1 + 1 - (b + 1) = 1 from by omega, one_mul]
        exact this
      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 * (b + 1) from by omega)
      have choose_sym : Nat.choose (2 * (b + 1)) (b + 2) = Nat.choose (2 * (b + 1)) b :=
        Nat.choose_symm_of_eq_add (by omega)
      have succ_mul_id : (2 * b + 3) * Nat.choose (2 * (b + 1)) b =
        Nat.choose (2 * b + 3) (b + 1) * (b + 1) := by
        have h := Nat.add_one_mul_choose_eq (2 * (b + 1)) b
        convert h using 2
      have choose_sym2 : Nat.choose (2 * b + 3) (b + 1) = Nat.choose (2 * b + 3) (b + 2) :=
        Nat.choose_symm_of_eq_add (by omega)
      nlinarith [choose_sym, succ_mul_id, choose_sym2]
  | case4 a b hle => omega

/--
[ballot_theorem_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BallotTheorem.lean)
-/
@[path]
lemma ballot_theorem_div
  {a b : ℕ}
-- given
  (hab : a > b) :
-- imply
  (ballotCount a b : ℚ) / Nat.choose (a + b) a = ((a : ℚ) - b) / (a + b) := by
-- proof
  have hab_sum_pos : (0 : ℚ) < a + b := by exact_mod_cast (show 0 < a + b by omega)
  have hchoose_pos : (0 : ℚ) < Nat.choose (a + b) a := by
    exact_mod_cast Nat.choose_pos (by omega : a ≤ a + b)
  rw [div_eq_div_iff (ne_of_gt hchoose_pos) (ne_of_gt hab_sum_pos)]
  calc (ballotCount a b : ℚ) * (↑a + ↑b)
    = ↑(ballotCount a b * (a + b)) := by push_cast; ring
    _ = ↑((a - b) * Nat.choose (a + b) a) := by exact_mod_cast ballot_theorem a b hab
    _ = (↑a - ↑b) * ↑(Nat.choose (a + b) a) := by push_cast [Nat.cast_sub (by omega : b ≤ a)]; ring


-- created on 2026-10-23
