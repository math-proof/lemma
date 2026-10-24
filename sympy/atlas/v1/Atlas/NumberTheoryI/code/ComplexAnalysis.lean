/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ComplexAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.OpenMapping
open Complex Set Filter Finset MeasureTheory Topology Metric

def ConvergesLocallyUniformlyOn (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (S : Set ℂ) : Prop :=
  TendstoLocallyUniformlyOn F f atTop S

def ConvergesNormallyOn (f : ℕ → ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∃ M : ℕ → ℝ, Summable M ∧ ∀ n, ∀ z ∈ S, ‖f n z‖ ≤ M n

def ConvergesLocallyNormallyOn (f : ℕ → ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z₀ ∈ S, ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ConvergesNormallyOn f (U ∩ S)


structure ParameterizedCurve where
  toFun : ℝ → ℂ
  a : ℝ
  b : ℝ
  hab : a ≤ b
  continuous_on : ContinuousOn toFun (Set.Icc a b)

instance : CoeFun ParameterizedCurve (fun _ => ℝ → ℂ) where
  coe := ParameterizedCurve.toFun

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
