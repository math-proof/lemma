/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Structure.v1.Atlas.ComplexVariables.code.Lecture13

@[expose] public section

noncomputable section

open Complex MeasureTheory Set intervalIntegral Real Filter Function Topology Metric

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

end ClosedCurve
end
