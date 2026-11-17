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

@[expose] public section

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
