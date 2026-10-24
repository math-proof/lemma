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

open Complex Filter

open scoped Topology

noncomputable section

/-- A complex function $f : \mathbb{C} \to \mathbb{C}$ is *holomorphic at* $z_0$
if it is complex-differentiable at $z_0$. -/
def HolomorphicAt (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  DifferentiableAt ℂ f z₀

/-- A complex function $f$ is *holomorphic on* an open set $\Omega \subseteq \mathbb{C}$
if it is complex-differentiable at every point of $\Omega$. -/
def HolomorphicOn (f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  DifferentiableOn ℂ f Ω

/-- A complex function is *entire* if it is holomorphic on all of $\mathbb{C}$. -/
def IsEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f

/-- $f$ has a *zero of order* $k$ at $z_0$ if $k > 0$ and locally
$f(z) = (z - z_0)^k g(z)$ for some analytic $g$ with $g(z_0) \neq 0$. -/
def HasZeroOfOrder (k : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  0 < k ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
    ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ k * g z

/-- $f$ has a *pole of order* $k$ at $z_0$ iff $1/f$ has a zero of order $k$ at $z_0$. -/
def HasPoleOfOrder (k : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  HasZeroOfOrder k f⁻¹ z₀

/-- $f$ has a *simple zero* at $z_0$ if it has a zero of order $1$ there. -/
def HasSimpleZero (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  HasZeroOfOrder 1 f z₀

/-- $f$ has a *simple pole* at $z_0$ if it has a pole of order $1$ there. -/
def HasSimplePole (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  HasPoleOfOrder 1 f z₀

/-- A function $f$ is *meromorphic on* an open set $\Omega$ if it is
meromorphic at every point of $\Omega$. -/
def IsMeromorphicOn (f : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  MeromorphicOn f Ω

/-- The *order* of $f$ at $z_0$, in $\mathbb{Z} \cup \{+\infty\}$: positive for
zeros, negative for poles, $+\infty$ if $f$ vanishes identically near $z_0$. -/
def ord (z₀ : ℂ) (f : ℂ → ℂ) : WithTop ℤ :=
  meromorphicOrderAt f z₀

end

open Set

/-- A *smooth curve* in $\mathbb{C}$: a continuously differentiable map
$\gamma : [a, b] \to \mathbb{C}$ on a real interval $[a, b]$. -/
structure SmoothCurve where
  a : ℝ
  b : ℝ
  hab : a ≤ b
  toFun : ℝ → ℂ
  contDiffOn : ContDiffOn ℝ 1 toFun (Icc a b)

namespace SmoothCurve

/-- Coerce a `SmoothCurve` to its underlying function $[a, b] \to \mathbb{C}$. -/
instance : CoeFun SmoothCurve (fun _ => ℝ → ℂ) := ⟨SmoothCurve.toFun⟩

/-- The image $\gamma([a, b]) \subseteq \mathbb{C}$ of a smooth curve. -/
def image (γ : SmoothCurve) : Set ℂ := γ.toFun '' Icc γ.a γ.b

/-- The *contour integral* of $f$ along a smooth curve $\gamma$:
$\int_\gamma f \, dz = \int_a^b f(\gamma(t)) \gamma'(t) \, dt$. -/
noncomputable def contourIntegral (f : ℂ → ℂ) (γ : SmoothCurve) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t

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
