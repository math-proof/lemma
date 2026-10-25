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
import Def.v1.Atlas.EllipticCurves.code.ComplexAnalysis.Part2
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
