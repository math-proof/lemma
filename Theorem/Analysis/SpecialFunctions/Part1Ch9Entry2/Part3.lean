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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry2.Part3
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

theorem exp_odd_mul_pi_I (n : ℤ) (hn : Odd n) :
    Complex.exp ((n : ℂ) * ↑Real.pi * Complex.I) = -1 := by
  have hEq : ((n : ℂ) * ↑Real.pi * Complex.I) = (n : ℂ) * (↑Real.pi * Complex.I) := by
    ring
  have hInt := Complex.exp_int_mul (↑Real.pi * Complex.I) n
  rw [hEq, hInt, Complex.exp_pi_mul_I]
  exact hn.neg_one_zpow

theorem one_add_E_ne_zero (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    1 + entry2E a ≠ 0 := by
  intro h
  have hE : entry2E a = -1 := by linear_combination h
  have hexp1 : Complex.exp (↑(Real.pi * (a - 1)) * Complex.I) = 1 := by
    have harg : ((↑(Real.pi * (a - 1)) : ℂ)) = ↑(Real.pi * a) - ↑Real.pi := by
      push_cast
      ring
    have hsplit : (↑(Real.pi * (a - 1)) * Complex.I : ℂ)
        = (↑(Real.pi * a) * Complex.I - ↑Real.pi * Complex.I) := by
      rw [harg]
      ring
    rw [hsplit, Complex.exp_sub, Complex.exp_pi_mul_I]
    unfold entry2E at hE
    rw [hE]
    simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  have him := congrArg Complex.im hn
  simp only [Complex.mul_I_im, Complex.ofReal_re] at him
  -- him : Real.pi * (a - 1) = (↑n * (2 * ↑Real.pi * Complex.I)).im
  -- simplify RHS to ↑n * (2 * Real.pi)
  have hRw : ((n : ℂ) * (2 * ↑Real.pi * Complex.I) : ℂ)
      = ((n : ℂ) * 2 * ↑Real.pi) * Complex.I := by ring
  rw [hRw, Complex.mul_I_im] at him
  simp only [Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero] at him
  -- him should now be Real.pi * (a - 1) = ↑n * (2 * Real.pi) in ℝ
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have ha_eq : a = (((2 * n + 1 : ℤ)) : ℝ) := by
    have h1 : Real.pi * (a - 1) = (n : ℝ) * 2 * Real.pi := him
    have h1' : Real.pi * (a - 1) = Real.pi * ((n : ℝ) * 2) := by linarith
    have h2 : a - 1 = (n : ℝ) * 2 := mul_left_cancel₀ hpi h1'
    have h3 : a = 2 * (n : ℝ) + 1 := by linarith
    have hcast : ((((2 * n + 1 : ℤ)) : ℝ)) = 2 * (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact h3
  exact ha n ha_eq

theorem exp_w_pi_eq_neg_E (a : ℝ) (j : ℤ) :
    Complex.exp (↑(Real.pi * (a - ((2 * j + 1 : ℤ) : ℝ))) * Complex.I)
      = -entry2E a := by
  have hOdd : Complex.exp (↑(((2 * j + 1 : ℤ) : ℝ)) * ↑Real.pi * Complex.I) = -1 :=
    exp_odd_mul_pi_I (2 * j + 1) ⟨j, rfl⟩
  have harg : ((↑(Real.pi * (a - ((2 * j + 1 : ℤ) : ℝ))) : ℂ))
      = ↑(Real.pi * a) - ↑(((2 * j + 1 : ℤ) : ℝ)) * ↑Real.pi := by
    push_cast
    ring
  have hsplit : (↑(Real.pi * (a - ((2 * j + 1 : ℤ) : ℝ))) * Complex.I : ℂ)
      = (↑(Real.pi * a) * Complex.I
        - ↑(((2 * j + 1 : ℤ) : ℝ)) * ↑Real.pi * Complex.I) := by
    rw [harg]
    ring
  rw [hsplit, Complex.exp_sub, hOdd]
  unfold entry2E
  field_simp

theorem h_periodic (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    entry2h a 0 = entry2h a Real.pi := by
  have hNe : 1 + entry2E a ≠ 0 := one_add_E_ne_zero a ha
  have hexp : Complex.exp (↑((a - 1) * Real.pi) * Complex.I) = -entry2E a := by
    have h0 := exp_w_pi_eq_neg_E a 0
    have hcast : ((((2 * (0 : ℤ) + 1 : ℤ)) : ℝ)) = 1 := by push_cast; ring
    have hEq : a - ((((2 * (0 : ℤ) + 1 : ℤ)) : ℝ)) = a - 1 := by rw [hcast]
    have hEq2 : Real.pi * (a - ((((2 * (0 : ℤ) + 1 : ℤ)) : ℝ))) = (a - 1) * Real.pi := by
      rw [hEq]; ring
    rw [hEq2] at h0
    exact h0
  have hAlg : (entry2A a + entry2B a * ↑Real.pi) * (-entry2E a) = entry2A a := by
    unfold entry2A entry2B
    have hNe2 : (1 + entry2E a) ^ 2 ≠ 0 := pow_ne_zero 2 hNe
    field_simp
    ring
  have h0eq : entry2h a 0 = entry2A a := by
    unfold entry2h
    simp
  have hpieq : entry2h a Real.pi
      = (entry2A a + entry2B a * ↑Real.pi) * (-entry2E a) := by
    unfold entry2h
    rw [hexp]
  rw [h0eq, hpieq]
  exact hAlg.symm

theorem h_continuous (a : ℝ) : Continuous (entry2h a) := by
  unfold entry2h
  fun_prop

end
end Entry2
end Ramanujan.Part1Ch9
end
