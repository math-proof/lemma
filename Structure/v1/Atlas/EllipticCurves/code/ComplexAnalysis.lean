/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Order
import Def.v1.Atlas.EllipticCurves.code.ComplexAnalysis
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

