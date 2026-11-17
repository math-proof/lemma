/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Analytic.Order
public import Def.v1.Atlas.EllipticCurves.code.ComplexAnalysis
public section

open Complex Filter

open scoped Topology

open Set


/-- A *smooth curve* in $\mathbb{C}$: a continuously differentiable map
$\gamma : [a, b] \to \mathbb{C}$ on a real interval $[a, b]$. -/
structure SmoothCurve where
  a : ℝ
  b : ℝ
  hab : a ≤ b
  toFun : ℝ → ℂ
  contDiffOn : ContDiffOn ℝ 1 toFun (Icc a b)

