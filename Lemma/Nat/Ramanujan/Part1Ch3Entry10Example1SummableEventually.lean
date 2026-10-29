import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example1SummableEventually

/--
[ramanujan_part1_ch3_entry10_example1_summable_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example1SummableEventually.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry10_example1_summable_eventually
  :
-- imply
  ∀ᶠ (x : ℝ) in Filter.atTop,
        Summable (fun j : ℕ => x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) /
            (↑(Nat.factorial (j + 1)) : ℝ)) := by
-- proof
  apply Filter.Eventually.of_forall
  intro x
  have hfact : ∀ j : ℕ, (0 : ℝ) < ((Nat.factorial (j + 1) : ℕ) : ℝ) := fun j =>
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hsqrt_le : ∀ j : ℕ, Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    intro j
    rw [Real.sqrt_le_self_iff]
    right
    have : 1 ≤ j + 1 := Nat.le_add_left 1 j
    exact_mod_cast this
  have hmajor :
    Summable (fun j : ℕ => (|x| ^ (j + 1) * ((j + 1 : ℕ) : ℝ)) /
      ((Nat.factorial (j + 1) : ℕ) : ℝ)) := by
    have hbase : Summable (fun j : ℕ => |x| ^ j / ((Nat.factorial j : ℕ) : ℝ)) :=
      Real.summable_pow_div_factorial |x|
    have h2 : Summable (fun j : ℕ => (|x| ^ j / ((Nat.factorial j : ℕ) : ℝ)) * |x|) :=
      hbase.mul_right |x|
    apply h2.congr (fun j => ?_)
    have hfj : ((Nat.factorial (j + 1) : ℕ) : ℝ) =
      ((j + 1 : ℕ) : ℝ) * ((Nat.factorial j : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hfj]
    field_simp
    ring
  apply Summable.of_norm_bounded hmajor
  intro j
  have hpos : (0 : ℝ) < ((Nat.factorial (j + 1) : ℕ) : ℝ) := hfact j
  have h1 : |Real.sqrt ((j + 1 : ℕ) : ℝ)| = Real.sqrt ((j + 1 : ℕ) : ℝ) :=
    abs_of_nonneg (Real.sqrt_nonneg _)
  have habs : |((Nat.factorial (j + 1) : ℕ) : ℝ)| = ((Nat.factorial (j + 1) : ℕ) : ℝ) :=
    abs_of_pos hpos
  have hle : Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := hsqrt_le j
  have hpow_nonneg : 0 ≤ |x| ^ (j + 1) := pow_nonneg (abs_nonneg _) _
  calc ‖x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) / (↑(Nat.factorial (j + 1)) : ℝ)‖
    = |x| ^ (j + 1) * Real.sqrt ((j + 1 : ℕ) : ℝ) / ((Nat.factorial (j + 1) : ℕ) : ℝ) := by
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, h1, habs]
    _ ≤ |x| ^ (j + 1) * ((j + 1 : ℕ) : ℝ) / ((Nat.factorial (j + 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
      exact mul_le_mul_of_nonneg_left hle hpow_nonneg

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example1SummableEventually


-- created on 2026-10-20
-- updated on 2026-10-28
