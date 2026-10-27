/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry13Bernoulligen.Part5
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry13Bernoulligen

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Topology MeasureTheory

noncomputable section

theorem entry13_C_hasDerivAt (j : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    HasDerivAt (fun y => entry13C (j + 1) r y) (entry13Cp j r x) x := by
  unfold entry13Cp
  by_cases hj : j = 0
  · subst hj
    simp only [ite_true, zero_add]
    exact entry13_C_one_hasDerivAt hr0 hr1 x
  · simp only [hj, ite_false]
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    exact entry13_C_succ_hasDerivAt j hj1 hr0 hr1 x

theorem entry13_Gterm_hasDerivAt (n j : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (x : ℝ) :
    HasDerivAt
      (fun y => entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * y ^ (n - j) * entry13C (j + 1) r y)
      (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x
          + x ^ (n - j) * entry13Cp j r x)) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ (n - j))
      (((n - j : ℕ) : ℝ) * x ^ (n - j - 1)) x :=
    hasDerivAt_pow (n - j) x
  have hA : HasDerivAt
      (fun y : ℝ => entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * y ^ (n - j))
      (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1))) x :=
    HasDerivAt.const_mul _ hpow
  have hC := entry13_C_hasDerivAt j hr0 hr1 x
  have h : HasDerivAt
      (fun y => (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * y ^ (n - j)) * entry13C (j + 1) r y)
      ((entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1))) * entry13C (j + 1) r x
        + (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ) * x ^ (n - j))
          * entry13Cp j r x) x :=
    HasDerivAt.fun_mul hA hC
  have hderiv : (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1))) * entry13C (j + 1) r x
        + (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ) * x ^ (n - j))
          * entry13Cp j r x
      = entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x
          + x ^ (n - j) * entry13Cp j r x) := by
    ring
  rw [hderiv] at h
  exact h

theorem entry13_cancel_pair (n j : ℕ) (hj : j < n) {r : ℝ} (x : ℝ) :
    (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x)
      + entry13s (j + 1) * (n.factorial : ℝ) / ((n - (j + 1)).factorial : ℝ)
        * (x ^ (n - (j + 1)) * entry13Cp (j + 1) r x)) = 0 := by
  have hCp : entry13Cp (j + 1) r x
      = entry13eps (j + 1) * entry13C (j + 1) r x := by
    unfold entry13Cp
    have hne : j + 1 ≠ 0 := by omega
    simp only [hne, ite_false]
  rw [hCp]
  have hnm : n - (j + 1) = n - j - 1 := by omega
  rw [hnm]
  obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
  have hfact : (n - j).factorial = (n - j) * (n - j - 1).factorial := by
    rw [hm, Nat.factorial_succ, Nat.add_sub_cancel]
  have hfactR : ((n - j).factorial : ℝ)
      = ((n - j : ℕ) : ℝ) * ((n - j - 1).factorial : ℝ) := by
    exact_mod_cast hfact
  have hnpos : 1 ≤ n - j := by omega
  have hd0 : ((n - j : ℕ) : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ ((n - j : ℕ) : ℝ) := by exact_mod_cast hnpos
    have h0 : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by linarith
    exact ne_of_gt h0
  have hg0 : ((n - j - 1).factorial : ℝ) ≠ 0 := by
    have hpos : 0 < ((n - j - 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    exact ne_of_gt hpos
  have hsign : entry13s (j + 1) * entry13eps (j + 1) = -entry13s j := by
    have h := entry13_sign_cancel (j + 1) (by omega)
    rwa [Nat.add_sub_cancel] at h
  have hfactor : (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x)
        + entry13s (j + 1) * (n.factorial : ℝ) / ((n - j - 1).factorial : ℝ)
          * (x ^ (n - j - 1)
            * (entry13eps (j + 1) * entry13C (j + 1) r x)))
      = x ^ (n - j - 1) * entry13C (j + 1) r x
        * ((entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ))
            * ((n - j : ℕ) : ℝ)
          + (entry13s (j + 1) * (n.factorial : ℝ)
            / ((n - j - 1).factorial : ℝ)) * entry13eps (j + 1)) := by
    ring
  rw [hfactor]
  have hbracket : (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ))
          * ((n - j : ℕ) : ℝ)
        + (entry13s (j + 1) * (n.factorial : ℝ)
          / ((n - j - 1).factorial : ℝ)) * entry13eps (j + 1)
      = 0 := by
    have h1 : (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ))
            * ((n - j : ℕ) : ℝ)
        = entry13s j * (n.factorial : ℝ) / ((n - j - 1).factorial : ℝ) := by
      rw [hfactR, div_mul_eq_mul_div,
        div_eq_div_iff (mul_ne_zero hd0 hg0) hg0]
      ring
    rw [h1]
    have h2 : (entry13s (j + 1) * (n.factorial : ℝ)
            / ((n - j - 1).factorial : ℝ)) * entry13eps (j + 1)
        = (entry13s (j + 1) * entry13eps (j + 1)) * (n.factorial : ℝ)
          / ((n - j - 1).factorial : ℝ) := by
      ring
    rw [h2, hsign]
    ring
  rw [hbracket, mul_zero]

end
end Entry13Bernoulligen
end Ramanujan.Part1Ch9
end
