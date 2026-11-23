/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ComplexAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.OpenMapping
public import Instance.v1.Atlas.NumberTheoryI.code.ComplexAnalysis

@[expose] public section

open Complex Set Filter Finset MeasureTheory Topology Metric


def ParameterizedCurve.IsClosed (γ : ParameterizedCurve) : Prop :=
  γ.toFun γ.a = γ.toFun γ.b

def ParameterizedCurve.IsSimple (γ : ParameterizedCurve) : Prop :=
  Set.InjOn γ.toFun (Set.Ico γ.a γ.b) ∧
  Set.InjOn γ.toFun (Set.Ioc γ.a γ.b)

noncomputable def contourIntegral (f : ℂ → ℂ) (γ : ParameterizedCurve) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t

def ParameterizedCurve.image (γ : ParameterizedCurve) : Set ℂ :=
  γ.toFun '' (Set.Icc γ.a γ.b)

opaque ParameterizedCurve.curveInterior (γ : ParameterizedCurve) : Set ℂ

def ParameterizedCurve.ContainedIn (γ : ParameterizedCurve) (U : Set ℂ) : Prop :=
  γ.image ⊆ U ∧ γ.curveInterior ⊆ U

noncomputable def complexResidue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (fun R => (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(z₀, R), f z)

