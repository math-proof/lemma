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
public import Def.v1.Atlas.EllipticCurves.code.ComplexAnalysis.Part2
public section

open Complex Filter

open scoped Topology

open Set


namespace SmoothCurve

/-- A *piecewise smooth curve* in $\mathbb{C}$: finitely many smooth pieces
$\gamma_0, \dots, \gamma_{n-1}$ glued end-to-end, with matching parameter
endpoints and continuous join. -/
structure PiecewiseSmoothCurve where
  n : ℕ
  hn : 0 < n
  pieces : Fin n → SmoothCurve
  endpoints_match : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    (pieces ⟨i.val + 1, hi⟩).a = (pieces i).b
  continuous_join : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
    (pieces i).toFun (pieces i).b =
    (pieces ⟨i.val + 1, hi⟩).toFun (pieces ⟨i.val + 1, hi⟩).a

end SmoothCurve
