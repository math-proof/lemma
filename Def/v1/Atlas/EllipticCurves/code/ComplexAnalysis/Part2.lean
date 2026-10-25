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
import Instance.v1.Atlas.EllipticCurves.code.ComplexAnalysis
open Complex Filter

open scoped Topology

open Set


namespace SmoothCurve

/-- The image $\gamma([a, b]) \subseteq \mathbb{C}$ of a smooth curve. -/
def image (γ : SmoothCurve) : Set ℂ := γ.toFun '' Icc γ.a γ.b

/-- The *contour integral* of $f$ along a smooth curve $\gamma$:
$\int_\gamma f \, dz = \int_a^b f(\gamma(t)) \gamma'(t) \, dt$. -/
noncomputable def contourIntegral (f : ℂ → ℂ) (γ : SmoothCurve) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t

end SmoothCurve
