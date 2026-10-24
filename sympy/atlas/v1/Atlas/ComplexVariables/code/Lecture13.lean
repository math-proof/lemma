/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity

import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Log

noncomputable section

open Complex MeasureTheory Set intervalIntegral Real Filter Function Topology Metric

structure ClosedCurve where
  toFun : ℝ → ℂ
  a : ℝ
  b : ℝ
  hab : a ≤ b
  continuous_toFun : ContinuousOn toFun (Icc a b)
  differentiable : DifferentiableOn ℝ toFun (Icc a b)
  continuous_deriv : ContinuousOn (deriv toFun) (Icc a b)
  closed : toFun a = toFun b

namespace ClosedCurve

variable (γ : ClosedCurve)

def range : Set ℂ := γ.toFun '' Icc γ.a γ.b

def LiesIn (Ω : Set ℂ) : Prop := γ.range ⊆ Ω

def windingNumber (w : ℂ) : ℂ :=
  (2 * ↑π * I)⁻¹ * ∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t

def IsHomologousToZero (Ω : Set ℂ) : Prop :=
  γ.LiesIn Ω ∧ ∀ a : ℂ, a ∉ Ω → γ.windingNumber a = 0

def contourIntegral (f : ℂ → ℂ) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t

def dividedDiff (f : ℂ → ℂ) : ℂ × ℂ → ℂ := fun p => dslope f p.1 p.2

open scoped Classical in
def ClosedCurve.complementDomain (γ : ClosedCurve) : Set ℂ :=
  {z : ℂ | z ∉ γ.range ∧ γ.windingNumber z = 0}

open scoped Classical in
def cauchyPiecewise (Ω : Set ℂ) (f : ℂ → ℂ) (γ : ClosedCurve) (z : ℂ) : ℂ :=
  if z ∈ Ω then
    (2 * ↑π * I)⁻¹ * γ.contourIntegral (fun ζ => dividedDiff f (z, ζ))
  else
    (2 * ↑π * I)⁻¹ * γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹)

noncomputable def cauchyTypeIntegral (f : ℂ → ℂ) (γ : ClosedCurve) (z : ℂ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * γ.contourIntegral (fun ζ => f ζ * (ζ - z)⁻¹)

abbrev RiemannSphere := OnePoint ℂ

def Set.toRiemannSphere (Ω : Set ℂ) : Set RiemannSphere :=
  OnePoint.some '' Ω

def Complex.IsSimplyConnected (Ω : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ IsConnected (Ω.toRiemannSphere)ᶜ
