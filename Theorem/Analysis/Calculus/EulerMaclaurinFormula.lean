/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
open scoped BigOperators

/-!
# Euler-Maclaurin formula
-/

public section


namespace Real.Calculus.EulerMaclaurinFormula

lemma coef_eq (j : ℕ) :
    ((bernoulli j : ℚ) : ℝ) = (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) := by
  by_cases hj : j = 1
  · subst hj
    have h : (bernoulli 1 : ℚ) = -1 / 2 := bernoulli_one
    simp [h]
  · simp [hj]

lemma bernoulliFun_eq_sum (p : ℕ) (x : ℝ) :
    bernoulliFun p x =
      ∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℝ) *
        (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) * x ^ (p - j) := by
  have hunfold : bernoulliFun p x =
      Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli p)) := rfl
  rw [hunfold, Polynomial.bernoulli_def, Polynomial.map_sum]
  rw [Polynomial.eval_finsetSum]
  have hterm : ∀ i ∈ Finset.range (p + 1),
      Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ)
        (Polynomial.monomial i (bernoulli (p - i) * ↑(p.choose i)))) =
      ((bernoulli (p - i) : ℚ) : ℝ) * (Nat.choose p i : ℝ) * x ^ i := by
    intro i _
    rw [Polynomial.map_monomial, Polynomial.eval_monomial]
    simp only [map_mul, map_natCast, eq_ratCast]
  rw [Finset.sum_congr rfl hterm]
  have hrefl : (∑ i ∈ Finset.range (p + 1),
      ((bernoulli (p - i) : ℚ) : ℝ) * (Nat.choose p i : ℝ) * x ^ i) =
      ∑ j ∈ Finset.range (p + 1),
        ((bernoulli j : ℚ) : ℝ) * (Nat.choose p (p - j) : ℝ) * x ^ (p - j) := by
    rw [← Finset.sum_range_reflect (fun j => ((bernoulli j : ℚ) : ℝ) *
      (Nat.choose p (p - j) : ℝ) * x ^ (p - j)) (p + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have e1 : p + 1 - 1 - i = p - i := by omega
    have e2 : p - (p - i) = i := by omega
    rw [e1, e2]
  rw [hrefl]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjle : j ≤ p := by omega
  have hc : (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) =
      ((bernoulli j : ℚ) : ℝ) := (coef_eq j).symm
  rw [hc, Nat.choose_symm hjle]
  ring

end Real.Calculus.EulerMaclaurinFormula
