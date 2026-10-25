/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Def.Analysis.Calculus.Bisection
/-!
This file constructs bisection sequences on real intervals and proves that their midpoints
converge to a bracketed root with the standard geometric error bound.
-/


namespace Real.Calculus.Bisection

theorem bisection_step_order
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (n : ℕ) (huvn : u n ≤ v n) :
    u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n := by
  rcases huv.2.2 n with h | h
  · rcases h with ⟨-, hu, hv⟩
    rw [hu, hv]
    exact ⟨by linarith, by linarith, le_rfl⟩
  · rcases h with ⟨-, hu, hv⟩
    rw [hu, hv]
    exact ⟨le_rfl, by linarith, by linarith⟩

theorem bisection_le_and_le
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (hab : a ≤ b) (huv : IsBisectionSequence f a b u v) :
    ∀ n, a ≤ u n ∧ u n ≤ v n ∧ v n ≤ b := by
  intro n
  induction n with
  | zero =>
      simp only [huv.1, huv.2.1]
      exact ⟨le_rfl, hab, le_rfl⟩
  | succ n ih =>
      obtain ⟨huu, huv', hvv⟩ := bisection_step_order huv n ih.2.1
      exact ⟨ih.1.trans huu, huv', hvv.trans ih.2.2⟩

theorem bisection_step_signs
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (n : ℕ)
    (hfu : f (u n) ≤ 0) (hfv : 0 ≤ f (v n)) :
    f (u (n + 1)) ≤ 0 ∧ 0 ≤ f (v (n + 1)) := by
  rcases huv.2.2 n with h | h
  · rcases h with ⟨hfm, hu, hv⟩
    rw [hu, hv]
    exact ⟨hfm, hfv⟩
  · rcases h with ⟨hfm, hu, hv⟩
    rw [hu, hv]
    exact ⟨hfu, hfm⟩

theorem bisection_invariants
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (hab : a ≤ b) (ha : f a ≤ 0) (hb : 0 ≤ f b)
    (huv : IsBisectionSequence f a b u v) :
    ∀ n, a ≤ u n ∧ u n ≤ v n ∧ v n ≤ b ∧ f (u n) ≤ 0 ∧ 0 ≤ f (v n) := by
  intro n
  induction n with
  | zero =>
      simp only [huv.1, huv.2.1]
      exact ⟨le_rfl, hab, le_rfl, ha, hb⟩
  | succ n ih =>
      obtain ⟨huu, huv', hvv⟩ := bisection_step_order huv n ih.2.1
      obtain ⟨hfu, hfv⟩ := bisection_step_signs huv n ih.2.2.2.1 ih.2.2.2.2
      exact ⟨ih.1.trans huu, huv', hvv.trans ih.2.2.1, hfu, hfv⟩

theorem bisection_nesting
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (hab : a ≤ b) (huv : IsBisectionSequence f a b u v) :
    ∀ n, u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n := by
  intro n
  exact bisection_step_order huv n (bisection_le_and_le hab huv n).2.1

theorem bisection_interval_length
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) :
    ∀ n, v n - u n = (b - a) / (2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp only [huv.1, huv.2.1, pow_zero, div_one]
  | succ n ih =>
      rcases huv.2.2 n with h | h
      · rcases h with ⟨-, hu, hv⟩
        rw [hu, hv]
        calc
          v n - (u n + v n) / 2 = (v n - u n) / 2 := by ring
          _ = ((b - a) / (2 : ℝ) ^ n) / 2 := by rw [ih]
          _ = (b - a) / (2 : ℝ) ^ (n + 1) := by
            rw [pow_succ]
            ring
      · rcases h with ⟨-, hu, hv⟩
        rw [hu, hv]
        calc
          (u n + v n) / 2 - u n = (v n - u n) / 2 := by ring
          _ = ((b - a) / (2 : ℝ) ^ n) / 2 := by rw [ih]
          _ = (b - a) / (2 : ℝ) ^ (n + 1) := by
            rw [pow_succ]
            ring

namespace IsBisectionSequence

/-- Every bisection interval stays ordered and inside the initial interval. -/
theorem le_and_le
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (hab : a ≤ b) (n : ℕ) :
    a ≤ u n ∧ u n ≤ v n ∧ v n ≤ b :=
  bisection_le_and_le hab huv n

/-- Every bisection interval stays ordered, inside the initial interval, and preserves signs. -/
theorem invariants
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (hab : a ≤ b)
    (ha : f a ≤ 0) (hb : 0 ≤ f b) (n : ℕ) :
    a ≤ u n ∧ u n ≤ v n ∧ v n ≤ b ∧ f (u n) ≤ 0 ∧ 0 ≤ f (v n) :=
  bisection_invariants hab ha hb huv n

/-- Consecutive bisection intervals are nested. -/
theorem nested
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (hab : a ≤ b) (n : ℕ) :
    u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n :=
  bisection_nesting hab huv n

/-- The length of the `n`th bisection interval is the initial length divided by `2 ^ n`. -/
theorem sub_eq
    {f : ℝ → ℝ} {a b : ℝ} {u v : ℕ → ℝ}
    (huv : IsBisectionSequence f a b u v) (n : ℕ) :
    v n - u n = (b - a) / (2 : ℝ) ^ n :=
  bisection_interval_length huv n

end IsBisectionSequence
end Real.Calculus.Bisection
