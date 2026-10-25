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
import Structure.v1.Atlas.EllipticCurves.code.ComplexAnalysis.Part2
open Complex Filter

open scoped Topology

open Set


namespace SmoothCurve

namespace PiecewiseSmoothCurve

/-- The starting parameter of a piecewise smooth curve (the $a$ of its first piece). -/
def a (γ : PiecewiseSmoothCurve) : ℝ := (γ.pieces ⟨0, γ.hn⟩).a

/-- The ending parameter of a piecewise smooth curve (the $b$ of its last piece). -/
def b (γ : PiecewiseSmoothCurve) : ℝ :=
  (γ.pieces ⟨γ.n - 1, Nat.sub_one_lt_of_lt γ.hn⟩).b

/-- The underlying function $\gamma : \mathbb{R} \to \mathbb{C}$ of a piecewise
smooth curve, defined piece-by-piece on the union of the parameter intervals
and $0$ outside. -/
noncomputable def toFun (γ : PiecewiseSmoothCurve) : ℝ → ℂ :=
  fun t =>
    if h : ∃ i : Fin γ.n, t ∈ Icc (γ.pieces i).a (γ.pieces i).b then
      (γ.pieces h.choose).toFun t
    else
      0

/-- A piecewise smooth curve is *simple* if $\gamma$ is injective on the
open parameter interval $(a, b)$. -/
def IsSimple (γ : PiecewiseSmoothCurve) : Prop :=
  InjOn γ.toFun (Ioo γ.a γ.b)

/-- A piecewise smooth curve is *closed* if its endpoints coincide:
$\gamma(a) = \gamma(b)$. -/
def IsClosed (γ : PiecewiseSmoothCurve) : Prop :=
  γ.toFun γ.a = γ.toFun γ.b

/-- The image of a piecewise smooth curve in $\mathbb{C}$: the union of the
images of its individual smooth pieces. -/
def image (γ : PiecewiseSmoothCurve) : Set ℂ :=
  ⋃ i : Fin γ.n, (γ.pieces i).toFun '' Icc (γ.pieces i).a (γ.pieces i).b

/-- The *interior region* enclosed by a (closed, simple) piecewise smooth curve,
in the sense of the Jordan curve theorem. -/
noncomputable def contourIntegral (f : ℂ → ℂ) (γ : PiecewiseSmoothCurve) : ℂ :=
  ∑ i : Fin γ.n, (γ.pieces i).contourIntegral f

/-- View a smooth curve as a (degenerate) piecewise smooth curve with a single piece. -/
def SmoothCurve.toPiecewiseSmoothCurve (γ : SmoothCurve) : PiecewiseSmoothCurve where
  n := 1
  hn := Nat.one_pos
  pieces := fun _ => γ
  endpoints_match := fun _ hi => absurd hi (by omega)
  continuous_join := fun _ hi => absurd hi (by omega)

namespace SmoothCurve

open MeasureTheory

/-- The *residue* $\mathrm{Res}_{z_0}(f)$ of a meromorphic function $f$ at
$z_0$, computed via the formula
$\frac{1}{(k-1)!} \lim_{z \to z_0} \frac{d^{k-1}}{dz^{k-1}}\bigl[(z - z_0)^k f(z)\bigr]$
for the meromorphic order $k$, and $0$ if $f$ is not meromorphic at $z_0$. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  if h : MeromorphicAt f z₀ then
    if h.choose = 0 then 0
    else iteratedDeriv (h.choose - 1) (fun z => (z - z₀) ^ h.choose • f z) z₀ /
      ((h.choose - 1).factorial : ℂ)
  else 0

end SmoothCurve
end PiecewiseSmoothCurve
end SmoothCurve
