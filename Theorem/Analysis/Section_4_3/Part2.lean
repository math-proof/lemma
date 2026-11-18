module

public import Mathlib
public import Abbrev.Analysis.Section_4_3.Part2


public section

namespace Section_4_3

/--
  Definition 4.3.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by
  rw [close_iff]
  simp

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  rw [close_iff, close_iff, abs_sub_comm]

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
  rw [close_iff] at *
  calc
    |x - z| = |(x - y) + (y - z)| := by ring
    _ ≤ |x - y| + |y - z| := abs_add_le _ _
    _ ≤ ε + δ := add_le_add hxy hyz

/-- Proposition 4.3.7(d) (addition) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x + z) (y + w) := by
  rw [close_iff] at *
  calc
    |(x + z) - (y + w)| = |(x - y) + (z - w)| := by ring
    _ ≤ |x - y| + |z - w| := abs_add_le _ _
    _ ≤ ε + δ := add_le_add hxy hzw

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add_le _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add_le]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- Definition 4.3.9 (exponentiation) (base case).  Here we use the Mathlib definition. -/
lemma pow_zero (x:ℚ) : x^0 = 1 := _root_.pow_zero x

lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

end Section_4_3
