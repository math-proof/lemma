import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.Bisection

open Real.Calculus.Bisection

/--
[IsBisectionSequence.le_and_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Bisection.lean)
-/
@[path]
private lemma isBisectionSequence_le_and_le_eq
-- given
  (huv : IsBisectionSequence f a b u v) (hab : a ≤ b) (n : ℕ) :
-- imply
  a ≤ u n ∧ u n ≤ v n ∧ v n ≤ b := by
-- proof
  apply huv.le_and_le hab n


/--
[IsBisectionSequence.invariants](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Bisection.lean)
-/
@[path]
private lemma isBisectionSequence_invariants_eq
-- given
  (huv : IsBisectionSequence f a b u v) (hab : a ≤ b)
  (ha : f a ≤ 0) (hb : 0 ≤ f b) (n : ℕ) :
-- imply
  a ≤ u n ∧ u n ≤ v n ∧ v n ≤ b ∧ f (u n) ≤ 0 ∧ 0 ≤ f (v n) := by
-- proof
  apply huv.invariants hab ha hb n


/--
[IsBisectionSequence.nested](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Bisection.lean)
-/
@[path]
private lemma isBisectionSequence_nested_eq
-- given
  (huv : IsBisectionSequence f a b u v) (hab : a ≤ b) (n : ℕ) :
-- imply
  u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n := by
-- proof
  apply huv.nested hab n


/--
[IsBisectionSequence.sub_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Bisection.lean)
-/
@[path]
private lemma isBisectionSequence_sub_eq_eq
-- given
  (huv : IsBisectionSequence f a b u v) (n : ℕ) :
-- imply
  v n - u n = (b - a) / (2 : ℝ) ^ n := by
-- proof
  apply huv.sub_eq n


/--
[exists_isBisectionSequence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Bisection.lean)
-/
@[path]
private lemma exists_isBisectionSequence_eq
-- given
  (f : ℝ → ℝ) (a b : ℝ) :
-- imply
  ∃ u v, IsBisectionSequence f a b u v := by
-- proof
  apply exists_isBisectionSequence f a b


/--
[exists_isBisectionSequence_nested](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Bisection.lean)
-/
@[path]
private lemma exists_isBisectionSequence_nested_eq
-- given
  (hab : a ≤ b) (ha : f a ≤ 0) (hb : 0 ≤ f b) :
-- imply
  ∃ u v : ℕ → ℝ, IsBisectionSequence f a b u v ∧
    (∀ n, u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n) ∧
    (∀ n, v n - u n = (b - a) / (2 : ℝ) ^ n) ∧
    ∀ n, f (u n) * f (v n) ≤ 0 := by
-- proof
  apply exists_isBisectionSequence_nested hab ha hb


/--
[bisection_nested_intervals](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Bisection.lean)
-/
@[path]
private lemma bisection_nested_intervals_eq
-- given
  (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
  (ha : f a ≤ 0) (hb : 0 ≤ f b) :
-- imply
  ∃ u v : ℕ → ℝ, IsBisectionSequence f a b u v ∧
    (∀ n, u n ≤ u (n + 1) ∧ u (n + 1) ≤ v (n + 1) ∧ v (n + 1) ≤ v n) ∧
    (∀ n, v n - u n = (b - a) / (2 : ℝ) ^ n) ∧
    ∀ n, f (u n) * f (v n) ≤ 0 := by
-- proof
  apply bisection_nested_intervals hab _ ha hb
  · exact hf


/--
[bisection_approximate_root_with_rate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Bisection.lean)
-/
@[path]
private lemma bisection_approximate_root_with_rate_eq
-- given
  (u v : ℕ → ℝ)
  (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
  (ha : f a ≤ 0) (hb : 0 ≤ f b) (huv : IsBisectionSequence f a b u v) :
-- imply
  ∃ c ∈ Set.Icc a b, f c = 0 ∧
    Filter.Tendsto (fun n => (u n + v n) / 2) Filter.atTop (nhds c) ∧
    ∀ n, |(u n + v n) / 2 - c| ≤ (b - a) / (2 : ℝ) ^ (n + 1) := by
-- proof
  apply bisection_approximate_root_with_rate hab hf ha hb u v huv


-- created on 2026-10-09
