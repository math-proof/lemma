/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/Wave3D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D

set_option maxHeartbeats 3200000

noncomputable section

open Matrix Real MeasureTheory Filter intervalIntegral

namespace WaveEquation3D

/-- Shorthand for $3$-dimensional Euclidean space $\mathbb{R}^3$ used as the
spatial domain for the wave equation. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Predicate stating that $u : \mathbb{R} \times \mathbb{R}^3 \to \mathbb{R}$
is a $C^2$ solution of the $3$-dimensional wave equation
$-\partial_t^2 u + \Delta u = 0$. -/
structure IsWaveSolution3D (u : ℝ → E3 → ℝ) : Prop where
  smooth : ContDiff ℝ 2 (fun p : ℝ × E3 => u p.1 p.2)
  wave_eq : ∀ t : ℝ, ∀ x : E3,
    fderiv ℝ (fun s => fderiv ℝ (fun s' => u s' x) s 1) t 1 =
    ∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (fun y' => u t y') y (EuclideanSpace.single i 1))
        x (EuclideanSpace.single i 1)

/-- Cauchy data for the $3$D wave equation: an initial position $f \in C^3(\mathbb{R}^3)$
and an initial velocity $g \in C^2(\mathbb{R}^3)$. -/
structure CauchyData3D where
  f : E3 → ℝ
  g : E3 → ℝ
  f_smooth : ContDiff ℝ 3 f
  g_smooth : ContDiff ℝ 2 g

/-- Conversion from spherical coordinates $(\theta, \varphi)$ on the unit sphere $S^2 \subset \mathbb{R}^3$
to Cartesian coordinates $(\sin\theta\cos\varphi, \sin\theta\sin\varphi, \cos\theta)$. -/
def sphericalToCart (θ φ : ℝ) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![sin θ * cos φ, sin θ * sin φ, cos θ]

/-- The spherical mean of $h : \mathbb{R}^3 \to \mathbb{R}$ over the sphere
$\partial B_r(x)$ of radius $r$ centred at $x$, defined via the spherical
parametrization
$\frac{1}{4\pi}\int_0^\pi\!\!\int_0^{2\pi} h(x + r\,\omega(\theta,\varphi))\sin\theta\,d\varphi\,d\theta$. -/
noncomputable def SphericalMean (h : E3 → ℝ) (x : E3) (r : ℝ) : ℝ :=
  (1 / (4 * π)) *
    ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
      h (x + r • sphericalToCart θ φ) * sin θ

/-- The surface integral $\int_{\partial B_r(x)} h\,d\sigma = 4\pi r^2 \cdot \mathrm{SphericalMean}\,h\,x\,r$
on the sphere of radius $r$ around $x$. -/
noncomputable def SphereIntegral (h : E3 → ℝ) (x : E3) (r : ℝ) : ℝ :=
  4 * π * r ^ 2 * SphericalMean h x r

/-- The integral over $\partial B_r(x)$ of the radial (outward normal) derivative of $h$,
expressed as $4\pi r^2$ times the radial derivative of the spherical mean. -/
noncomputable def SphereIntegralNormalDeriv (h : E3 → ℝ) (x : E3) (r : ℝ) : ℝ :=
  4 * π * r ^ 2 * deriv (fun ρ => SphericalMean h x ρ) r

/-- The "tilde" initial position: $\tilde F(r, x) := r \cdot \mathrm{SphericalMean}(f)(x, r)$,
the spatial profile of the auxiliary $1+1$-dimensional wave problem associated with $u$. -/
def F_tilde (data : CauchyData3D) (r : ℝ) (x : E3) : ℝ :=
  r * SphericalMean data.f x r

/-- The "tilde" initial velocity: $\tilde G(r, x) := r \cdot \mathrm{SphericalMean}(g)(x, r)$. -/
def G_tilde (data : CauchyData3D) (r : ℝ) (x : E3) : ℝ :=
  r * SphericalMean data.g x r

/-- **Kirchhoff's formula** (Class Meeting #12, Theorem 1.1). The unique
$C^2$ solution of the $3$-dimensional Cauchy problem
$-\partial_t^2 u + \Delta u = 0$, $u(0,x) = f(x)$, $\partial_t u(0,x) = g(x)$
admits the representation
$u(t, x) = \frac{1}{4\pi t^2}\int_{\partial B_t(x)} f\,d\sigma
+ \frac{1}{4\pi t}\int_{\partial B_t(x)} \nabla_{\hat N} f\,d\sigma
+ \frac{1}{4\pi t}\int_{\partial B_t(x)} g\,d\sigma$ for $t > 0$. -/
def sphericalAverage (u : ℝ → E3 → ℝ) (t r : ℝ) (x : E3) : ℝ :=
  SphericalMean (u t) x r

/-- The radius-weighted spherical average $r \cdot \mathrm{SphericalMean}(u(t,\cdot))(x, r)$,
which solves a $1+1$-dimensional half-line wave equation in $(t, r)$. -/
def sphericalAverage_tilde (u : ℝ → E3 → ℝ) (t r : ℝ) (x : E3) : ℝ :=
  r * sphericalAverage u t r x

/-- Initial velocity of the weighted spherical average: $\partial_t \tilde A(0, r, x) = \tilde G(r, x)$. -/
def minkowskiMetric (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => if i = j then (if (i : ℕ) = 0 then -1 else 1) else 0

/-- The Minkowski inner product $m(X, Y) = X^\alpha m_{\alpha\beta} Y^\beta$
on $\mathbb{R}^{1+n}$. -/
def minkowskiInner (n : ℕ) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  dotProduct X (minkowskiMetric n *ᵥ Y)

/-- A vector $X \in \mathbb{R}^{1+n}$ is **timelike** if $m(X, X) < 0$
(Definition 2.0.1, case (1)). -/
def IsTimelike (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X < 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **spacelike** if $m(X, X) > 0$
(Definition 2.0.1, case (2)). -/
def IsSpacelike (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X > 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **null** if $m(X, X) = 0$
(Definition 2.0.1, case (3)). -/
def IsNull (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X = 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **causal** if it is timelike or null,
equivalently $m(X, X) \le 0$ (Definition 2.0.1, case (4)). -/
def IsCausal (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X ≤ 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **future-directed** if its time component
satisfies $X^0 > 0$ (Definition 2.0.2). -/
def IsFutureDirected (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  X 0 > 0

/-- A matrix $\Lambda$ is a **Lorentz transformation** if it preserves the Minkowski
metric: $\Lambda^T m \Lambda = m$ (Definition 2.1.1). -/
def IsLorentzTransformation (n : ℕ) (Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  Λᵀ * minkowskiMetric n * Λ = minkowskiMetric n

/-- A **null frame** on $\mathbb{R}^{1+n}$ (Definition 2.2.1):
a basis $\{L, \underline L, e_{(1)}, \dots, e_{(n-1)}\}$ where $L, \underline L$ are null
with $m(L, \underline L) = -2$, and the $e_{(i)}$ are $m$-orthonormal vectors $m$-orthogonal
to both $L$ and $\underline L$. The `completeness` field records the resulting expansion
$X = -\tfrac12 m(\underline L, X) L - \tfrac12 m(L, X)\underline L + \sum_i m(e_{(i)}, X) e_{(i)}$. -/
structure NullFrame (n : ℕ) where
  L : Fin (n + 1) → ℝ
  Lb : Fin (n + 1) → ℝ
  e : Fin (n - 1) → (Fin (n + 1) → ℝ)
  L_null : minkowskiInner n L L = 0
  Lb_null : minkowskiInner n Lb Lb = 0
  L_Lb_inner : minkowskiInner n L Lb = -2
  e_orthonormal : ∀ i j : Fin (n - 1),
    minkowskiInner n (e i) (e j) = if i = j then 1 else 0
  L_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n L (e i) = 0
  Lb_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n Lb (e i) = 0
  completeness : ∀ X : Fin (n + 1) → ℝ,
    X = (-(1/2) * minkowskiInner n Lb X) • L
      + (-(1/2) * minkowskiInner n L X) • Lb
      + ∑ i, (minkowskiInner n (e i) X) • (e i)

/-- The **angular metric** $h(X, Y) := \sum_i m(e_{(i)}, X) m(e_{(i)}, Y)$ associated
with a null frame; it is positive-definite on the $m$-orthogonal complement of
$\mathrm{span}(L, \underline L)$ and vanishes on $\mathrm{span}(L, \underline L)$. -/
def angularMetric (n : ℕ) (nf : NullFrame n) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n - 1), minkowskiInner n (nf.e i) X * minkowskiInner n (nf.e i) Y
