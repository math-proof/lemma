/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Duhamel's variation of constants formula

This file proves existence, the differential equation, and uniqueness for the explicit
variation-of-constants solution of an inhomogeneous linear ODE on a real Banach space.
-/

open MeasureTheory

namespace ODE.DuhamelWanted

/-- The derivative of the homogeneous propagator applied to a fixed vector. -/
private theorem duhamel_hasDerivAt_exp_sub_smul_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (t₀ t : ℝ) (x₀ : E) :
    HasDerivAt (fun s => (NormedSpace.exp ((s - t₀) • A)) x₀)
      (A ((NormedSpace.exp ((t - t₀) • A)) x₀)) t := by
  have h_exp := hasDerivAt_exp_smul_const' A (t - t₀)
  have h_shift := h_exp.comp_sub_const t t₀
  have h_const : HasDerivAt (fun _ : ℝ => x₀) 0 t := hasDerivAt_const t x₀
  simpa [mul_apply_eq_comp] using h_shift.clm_apply h_const

private theorem duhamel_exp_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (t s : ℝ) :
    NormedSpace.exp ((t - s) • A) =
      NormedSpace.exp (t • A) * NormedSpace.exp ((-s) • A) := by
  let +nondep : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  simpa [sub_eq_add_neg, add_smul] using NormedSpace.exp_add_of_commute
    (((Commute.refl A).smul_left t).smul_right (-s))

private theorem duhamel_exp_mul_exp_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (t : ℝ) :
    NormedSpace.exp (t • A) * NormedSpace.exp ((-t) • A) = 1 := by
  simpa using (duhamel_exp_sub A t t).symm

private theorem duhamel_integrand_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (b : ℝ → E) (hb : Continuous b) :
    Continuous (fun s => (NormedSpace.exp ((-s) • A)) (b s)) := by
  have h_exp : Continuous (fun s : ℝ => NormedSpace.exp (s • A)) :=
    (differentiable_exp_smul_const ℝ A).continuous
  exact (h_exp.comp continuous_id.neg).clm_apply hb

private theorem duhamel_integral_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (b : ℝ → E) (hb : Continuous b) (t₀ t : ℝ) :
    (∫ s in t₀..t, (NormedSpace.exp ((t - s) • A)) (b s)) =
      (NormedSpace.exp (t • A))
        (∫ s in t₀..t, (NormedSpace.exp ((-s) • A)) (b s)) := by
  have h_integrable : IntervalIntegrable
      (fun s => (NormedSpace.exp ((-s) • A)) (b s)) volume t₀ t :=
    (duhamel_integrand_continuous A b hb).intervalIntegrable t₀ t
  calc
    (∫ s in t₀..t, (NormedSpace.exp ((t - s) • A)) (b s)) =
        ∫ s in t₀..t, (NormedSpace.exp (t • A))
          ((NormedSpace.exp ((-s) • A)) (b s)) := by
      apply intervalIntegral.integral_congr
      intro s _
      change (NormedSpace.exp ((t - s) • A)) (b s) =
        (NormedSpace.exp (t • A)) ((NormedSpace.exp ((-s) • A)) (b s))
      rw [duhamel_exp_sub A t s, mul_apply_eq_comp]
    _ = (NormedSpace.exp (t • A))
        (∫ s in t₀..t, (NormedSpace.exp ((-s) • A)) (b s)) :=
      (NormedSpace.exp (t • A)).intervalIntegral_comp_comm h_integrable

private theorem duhamel_integral_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (b : ℝ → E) (hb : Continuous b) (t₀ t : ℝ) :
    HasDerivAt
      (fun u => ∫ s in t₀..u, (NormedSpace.exp ((u - s) • A)) (b s))
      (A (∫ s in t₀..t, (NormedSpace.exp ((t - s) • A)) (b s)) + b t) t := by
  have hf := duhamel_integrand_continuous A b hb
  have h_primitive : HasDerivAt
      (fun u => ∫ s in t₀..u, (NormedSpace.exp ((-s) • A)) (b s))
      ((NormedSpace.exp ((-t) • A)) (b t)) t :=
    (hf.integral_hasStrictDerivAt t₀ t).hasDerivAt
  have h_product := (hasDerivAt_exp_smul_const' A t).clm_apply h_primitive
  have h_original := h_product.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => duhamel_integral_eq A b hb t₀ u)
  refine h_original.congr_deriv ?_
  have h_cancel : (NormedSpace.exp (t • A))
      ((NormedSpace.exp ((-t) • A)) (b t)) = b t := by
    rw [← mul_apply_eq_comp, duhamel_exp_mul_exp_neg A t]
    rfl
  rw [mul_apply_eq_comp, ← duhamel_integral_eq A b hb t₀ t, h_cancel]

private theorem duhamel_solution_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (b : ℝ → E) (t₀ : ℝ) (x₀ : E) (hb : Continuous b) (t : ℝ) :
    HasDerivAt
      (fun u => (NormedSpace.exp ((u - t₀) • A)) x₀ +
        ∫ s in t₀..u, (NormedSpace.exp ((u - s) • A)) (b s))
      (A ((NormedSpace.exp ((t - t₀) • A)) x₀ +
        ∫ s in t₀..t, (NormedSpace.exp ((t - s) • A)) (b s)) + b t) t := by
  have h_homogeneous := duhamel_hasDerivAt_exp_sub_smul_apply A t₀ t x₀
  have h_forced := duhamel_integral_hasDerivAt A b hb t₀ t
  convert h_homogeneous.add h_forced using 1
  rw [map_add, add_assoc]

private theorem duhamel_solution_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (b : ℝ → E) (t₀ : ℝ) (x y : ℝ → E)
    (hx : ∀ t, HasDerivAt x (A (x t) + b t) t)
    (hy : ∀ t, HasDerivAt y (A (y t) + b t) t) (h₀ : x t₀ = y t₀) : x = y := by
  apply ODE_solution_unique_univ (v := fun t z => A z + b t)
    (s := fun _ => Set.univ) (K := ‖A‖₊)
  · intro t
    simpa using
      A.lipschitzWith.add (LipschitzWith.const (α := E) (b t))
  · intro t
    exact ⟨hx t, Set.mem_univ _⟩
  · intro t
    exact ⟨hy t, Set.mem_univ _⟩
  · exact h₀

/-- Duhamel's formula (variation of constants): for a bounded linear operator
`A` and continuous forcing `b`, the function built from the operator
exponential solves `x' = A x + b` from `x₀`, and it is the unique solution.
Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential equations`, entry `method of constant variation
(Duhamel's formula)` (unmapped);
G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 3.2;
stable ref https://en.wikipedia.org/wiki/Duhamel%27s_principle.

Proves `Wanted` entry `duhamel_variation_of_constants`.

Proof: Factor the propagator by the commuting exponential group law, differentiate the
integrating-factor primitive, and apply global Lipschitz uniqueness. This follows Teschl,
Sections 3.2 and 3.4, formula (3.48) and Theorem 3.12 / (3.97).
-/
theorem duhamel_variation_of_constants
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (b : ℝ → E) (t₀ : ℝ) (x₀ : E)
    (hb : Continuous b) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧
      (∀ t, x t = (NormedSpace.exp ((t - t₀) • A)) x₀ +
        ∫ s in t₀..t, (NormedSpace.exp ((t - s) • A)) (b s)) ∧
      (∀ t, HasDerivAt x (A (x t) + b t) t) ∧
      ∀ y : ℝ → E, y t₀ = x₀ → (∀ t, HasDerivAt y (A (y t) + b t) t) → y = x := by
  let x : ℝ → E := fun t => (NormedSpace.exp ((t - t₀) • A)) x₀ +
    ∫ s in t₀..t, (NormedSpace.exp ((t - s) • A)) (b s)
  have hx₀ : x t₀ = x₀ := by
    simp [x]
  have hx_deriv : ∀ t, HasDerivAt x (A (x t) + b t) t := by
    intro t
    simpa only [x] using duhamel_solution_hasDerivAt A b t₀ x₀ hb t
  refine ⟨x, hx₀, fun _ => rfl, hx_deriv, ?_⟩
  intro y hy₀ hy_deriv
  exact duhamel_solution_unique A b t₀ y x hy_deriv hx_deriv (hy₀.trans hx₀.symm)

end ODE.DuhamelWanted
