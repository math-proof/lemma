/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Order.LeftRightNhds
import Theorem.Analysis.Complex.LoomanMenchoff.Part3
/-!
# The Looman–Menchoff theorem

This file proves that a continuous complex-valued function with everywhere-existing partial
derivatives satisfying the Cauchy–Riemann equations is complex differentiable.
-/


namespace MetaMathlibExt

open Set Filter MeasureTheory Metric Finset

open BoxIntegral

open scoped ENNReal Interval NNReal Topology BoxIntegral Matrix

noncomputable section

def loomanBoxPoint (x y : ℝ) : ℂ := x + y * Complex.I

def loomanBoundary (f : ℂ → ℂ) (J : Box (Fin 2)) : ℂ :=
  (∫ x in J.lower 0..J.upper 0,
      f (loomanBoxPoint x (J.lower 1)) - f (loomanBoxPoint x (J.upper 1))) +
    Complex.I * ∫ y in J.lower 1..J.upper 1,
      f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y)

noncomputable def loomanBoundary_boxAdditive (f : ℂ → ℂ) (hf : Continuous f)
    (I : Box (Fin 2)) : Fin 2 →ᵇᵃ[I] ℂ := by
  apply BoxAdditiveMap.ofMapSplitAdd (loomanBoundary f) I
  intro J hJI i x hx
  fin_cases i
  · rw [Box.splitLower_def hx, Box.splitUpper_def hx]
    simp only [Option.elim']
    simp only [Fin.zero_eta, Fin.isValue]
    have hh₁ : IntervalIntegrable
        (fun t : ℝ ↦ f (loomanBoxPoint t (J.lower 1)) -
          f (loomanBoxPoint t (J.upper 1))) volume (J.lower 0) x :=
      (show Continuous (fun t : ℝ ↦ f (loomanBoxPoint t (J.lower 1)) -
        f (loomanBoxPoint t (J.upper 1))) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hh₂ : IntervalIntegrable
        (fun t : ℝ ↦ f (loomanBoxPoint t (J.lower 1)) -
          f (loomanBoxPoint t (J.upper 1))) volume x (J.upper 0) :=
      (show Continuous (fun t : ℝ ↦ f (loomanBoxPoint t (J.lower 1)) -
        f (loomanBoxPoint t (J.upper 1))) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hv₁ : IntervalIntegrable
        (fun y : ℝ ↦ f (loomanBoxPoint x y) -
          f (loomanBoxPoint (J.lower 0) y)) volume (J.lower 1) (J.upper 1) :=
      (show Continuous (fun y : ℝ ↦ f (loomanBoxPoint x y) -
        f (loomanBoxPoint (J.lower 0) y)) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hv₂ : IntervalIntegrable
        (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
          f (loomanBoxPoint x y)) volume (J.lower 1) (J.upper 1) :=
      (show Continuous (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
        f (loomanBoxPoint x y)) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    calc
      ((∫ t in J.lower 0..x,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ∫ y in J.lower 1..J.upper 1,
            f (loomanBoxPoint x y) - f (loomanBoxPoint (J.lower 0) y)) +
        ((∫ t in x..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ∫ y in J.lower 1..J.upper 1,
            f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint x y)) =
        ((∫ t in J.lower 0..x,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t (J.upper 1))) +
          ∫ t in x..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ((∫ y in J.lower 1..J.upper 1,
            f (loomanBoxPoint x y) - f (loomanBoxPoint (J.lower 0) y)) +
            ∫ y in J.lower 1..J.upper 1,
              f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint x y)) := by ring
      _ = (∫ t in J.lower 0..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ((∫ y in J.lower 1..J.upper 1,
            f (loomanBoxPoint x y) - f (loomanBoxPoint (J.lower 0) y)) +
            ∫ y in J.lower 1..J.upper 1,
              f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint x y)) := by
        rw [intervalIntegral.integral_add_adjacent_intervals hh₁ hh₂]
      _ = _ := by
        rw [← intervalIntegral.integral_add hv₁ hv₂]
        congr 2
        apply intervalIntegral.integral_congr
        intro y _
        ring
  · rw [Box.splitLower_def hx, Box.splitUpper_def hx]
    simp only [Option.elim']
    simp only [Fin.mk_one, Fin.isValue]
    have hh₁ : IntervalIntegrable
        (fun t : ℝ ↦ f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t x))
        volume (J.lower 0) (J.upper 0) :=
      (show Continuous (fun t : ℝ ↦
        f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t x)) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hh₂ : IntervalIntegrable
        (fun t : ℝ ↦ f (loomanBoxPoint t x) - f (loomanBoxPoint t (J.upper 1)))
        volume (J.lower 0) (J.upper 0) :=
      (show Continuous (fun t : ℝ ↦
        f (loomanBoxPoint t x) - f (loomanBoxPoint t (J.upper 1))) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hv₁ : IntervalIntegrable
        (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
          f (loomanBoxPoint (J.lower 0) y)) volume (J.lower 1) x :=
      (show Continuous (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
        f (loomanBoxPoint (J.lower 0) y)) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    have hv₂ : IntervalIntegrable
        (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
          f (loomanBoxPoint (J.lower 0) y)) volume x (J.upper 1) :=
      (show Continuous (fun y : ℝ ↦ f (loomanBoxPoint (J.upper 0) y) -
        f (loomanBoxPoint (J.lower 0) y)) by
          unfold loomanBoxPoint
          fun_prop).intervalIntegrable _ _
    calc
      ((∫ t in J.lower 0..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t x)) +
          Complex.I * ∫ y in J.lower 1..x,
            f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y)) +
        ((∫ t in J.lower 0..J.upper 0,
            f (loomanBoxPoint t x) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ∫ y in x..J.upper 1,
            f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y)) =
          ((∫ t in J.lower 0..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t x)) +
            ∫ t in J.lower 0..J.upper 0,
              f (loomanBoxPoint t x) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ((∫ y in J.lower 1..x,
            f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y)) +
            ∫ y in x..J.upper 1,
              f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y)) := by
        ring
      _ = ((∫ t in J.lower 0..J.upper 0,
            f (loomanBoxPoint t (J.lower 1)) - f (loomanBoxPoint t x)) +
            ∫ t in J.lower 0..J.upper 0,
              f (loomanBoxPoint t x) - f (loomanBoxPoint t (J.upper 1))) +
          Complex.I * ∫ y in J.lower 1..J.upper 1,
            f (loomanBoxPoint (J.upper 0) y) - f (loomanBoxPoint (J.lower 0) y) := by
        rw [intervalIntegral.integral_add_adjacent_intervals hv₁ hv₂]
      _ = _ := by
        rw [← intervalIntegral.integral_add hh₁ hh₂]
        congr 2
        funext t
        ring

end
end MetaMathlibExt
