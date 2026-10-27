/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.AddCircle.Defs
import Def.Analysis.SpecialFunctions.Part1Ch9Entry2.Part5
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry2

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem hasDerivAt_ofReal_id (x : ℝ) :
    HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 x := by
  have hId : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
  simpa using hId.ofReal_comp

theorem hasDerivAt_G_aux (a : ℝ) (j : ℤ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => entry2G a j y)
      ((entry2A a + entry2B a * ↑x)
        * Complex.exp (((↑(entry2w a j)) * Complex.I) * ↑x)) x := by
  have hw : (↑(entry2w a j) : ℂ) ≠ 0 := by
    exact_mod_cast w_ne_zero a ha j
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hwI : ((↑(entry2w a j) : ℂ) * Complex.I) ≠ 0 := mul_ne_zero hw hI
  -- ℂ→ℂ linear part, then restrict with comp_ofReal
  have hFc : HasDerivAt (fun z : ℂ => (((↑(entry2w a j) : ℂ) * Complex.I) * z))
      ((↑(entry2w a j) : ℂ) * Complex.I) (↑x : ℂ) := by
    simpa using (hasDerivAt_const_mul (((↑(entry2w a j) : ℂ) * Complex.I)) (x := (↑x : ℂ)))
  have hF : HasDerivAt (fun y : ℝ => (((↑(entry2w a j) : ℂ) * Complex.I) * ↑y))
      ((↑(entry2w a j) : ℂ) * Complex.I) x :=
    hFc.comp_ofReal
  have hE : HasDerivAt (fun y : ℝ => Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑y)))
      (Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x))
        * ((↑(entry2w a j) : ℂ) * Complex.I)) x :=
    hF.cexp
  have hBc : HasDerivAt (fun z : ℂ => entry2B a * z) (entry2B a) (↑x : ℂ) := by
    simpa using (hasDerivAt_const_mul (entry2B a) (x := (↑x : ℂ)))
  have hB : HasDerivAt (fun y : ℝ => entry2B a * (↑y : ℂ)) (entry2B a) x :=
    hBc.comp_ofReal
  have hABc : HasDerivAt (fun z : ℂ => entry2A a + entry2B a * z)
      (entry2B a) (↑x : ℂ) := by
    have h1 : HasDerivAt (fun _ : ℂ => entry2A a) 0 (↑x : ℂ) := hasDerivAt_const _ _
    have h2 := h1.fun_add hBc
    simpa using h2
  have hAB : HasDerivAt (fun y : ℝ => entry2A a + entry2B a * (↑y : ℂ))
      (entry2B a) x :=
    hABc.comp_ofReal
  have hDiv : HasDerivAt
      (fun y : ℝ => (entry2A a + entry2B a * (↑y : ℂ))
        / ((↑(entry2w a j) : ℂ) * Complex.I))
      (entry2B a / ((↑(entry2w a j) : ℂ) * Complex.I)) x :=
    hAB.div_const _
  have hL : HasDerivAt
      (fun y : ℝ => (entry2A a + entry2B a * (↑y : ℂ))
        / ((↑(entry2w a j) : ℂ) * Complex.I)
        + entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2))
      (entry2B a / ((↑(entry2w a j) : ℂ) * Complex.I)) x := by
    have h2 : HasDerivAt (fun _ : ℝ => entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2))
        0 x := hasDerivAt_const _ _
    have h3 := hDiv.fun_add h2
    simpa using h3
  have hG := hE.fun_mul hL
  have hEq : (Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x))
        * ((↑(entry2w a j) : ℂ) * Complex.I))
        * ((entry2A a + entry2B a * ↑x) / ((↑(entry2w a j) : ℂ) * Complex.I)
          + entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2))
        + Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x))
          * (entry2B a / ((↑(entry2w a j) : ℂ) * Complex.I))
      = (entry2A a + entry2B a * ↑x)
        * Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x)) := by
    have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
    field_simp
    linear_combination entry2B a * hII
  have hGoal : (fun y : ℝ => entry2G a j y)
      = (fun y : ℝ => Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑y))
        * ((entry2A a + entry2B a * ↑y) / ((↑(entry2w a j) : ℂ) * Complex.I)
          + entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2))) := by
    ext y
    simp only [entry2G]
  rw [hGoal]
  rw [hEq] at hG
  exact hG

theorem hasDerivAt_G (a : ℝ) (j : ℤ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (x : ℝ) :
    HasDerivAt (entry2G a j)
      ((entry2A a + entry2B a * ↑x)
        * Complex.exp (((↑(entry2w a j)) * Complex.I) * ↑x)) x :=
  hasDerivAt_G_aux a j ha x

theorem integral_eq_pi_div_w2 (a : ℝ) (j : ℤ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    (∫ x in (0 : ℝ)..Real.pi,
      (entry2A a + entry2B a * (↑x : ℂ))
        * Complex.exp (((↑(entry2w a j) : ℂ) * Complex.I) * ↑x))
      = (↑Real.pi : ℂ) / (((↑(entry2w a j) : ℂ)) ^ 2) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (entry2G a j)
        ((entry2A a + entry2B a * (↑x : ℂ))
          * Complex.exp (((↑(entry2w a j) : ℂ) * Complex.I) * ↑x)) x := by
    intro x _
    exact hasDerivAt_G a j ha x
  have hcont : Continuous (fun x : ℝ =>
      (entry2A a + entry2B a * (↑x : ℂ))
        * Complex.exp (((↑(entry2w a j) : ℂ) * Complex.I) * ↑x)) := by
    fun_prop
  have hint : IntervalIntegrable (fun x : ℝ =>
      (entry2A a + entry2B a * (↑x : ℂ))
        * Complex.exp (((↑(entry2w a j) : ℂ) * Complex.I) * ↑x))
      MeasureTheory.volume (0 : ℝ) Real.pi :=
    hcont.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC]
  -- compute G π - G 0
  have hw : (↑(entry2w a j) : ℂ) ≠ 0 := by
    exact_mod_cast w_ne_zero a ha j
  have hNe : 1 + entry2E a ≠ 0 := one_add_E_ne_zero a ha
  have hexp_pi : Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑Real.pi))
      = -entry2E a := by
    have h0 := exp_w_pi_eq_neg_E a j
    have hEq3 : ((↑(Real.pi * (a - ((2 * j + 1 : ℤ) : ℝ))) : ℂ) * Complex.I)
        = ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑Real.pi)) := by
      unfold entry2w
      push_cast
      ring
    rw [hEq3] at h0
    exact h0
  have hexp_0 : Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ((0 : ℝ) : ℂ)))
      = 1 := by
    simp
  have hGpi : entry2G a j Real.pi
      = (-entry2E a) * ((entry2A a + entry2B a * ↑Real.pi)
        / ((↑(entry2w a j) : ℂ) * Complex.I)
        + entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2)) := by
    unfold entry2G
    rw [hexp_pi]
  have hG0 : entry2G a j 0
      = (entry2A a) / ((↑(entry2w a j) : ℂ) * Complex.I)
        + entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2) := by
    unfold entry2G
    simp
  rw [hGpi, hG0]
  unfold entry2A entry2B
  field_simp
  ring

end
end Entry2
end Ramanujan.Part1Ch9
end
