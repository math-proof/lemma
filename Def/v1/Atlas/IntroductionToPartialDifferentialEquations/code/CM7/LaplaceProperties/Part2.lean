/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplaceProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties.Part2
open Set Metric MeasureTheory Topology Filter


noncomputable section

namespace CM7

/-- The predicate that $u$ solves Poisson's equation $\Delta u = f$ on $\Omega$, i.e. for
every $x \in \Omega$, $\Delta u(x) = f(x)$. -/
def IsPoisson {n : ℕ} (u : (Fin n → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ)
    (Ω : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ Ω, Laplacian n u x = f x

/-- The Dirichlet energy $\int_\Omega \|\nabla u(x)\|^2\, dx$ of $u$ on $\Omega$. -/
noncomputable def gradNormSquaredIntegral {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : ℝ :=
  ∫ x in Ω, ‖fderiv ℝ u x‖ ^ 2

/-- The outward unit normal vector field on the boundary of a domain in $\mathbb{R}^n$.
Provided abstractly as an opaque function. -/
opaque outwardUnitNormal (n : ℕ) : (Fin n → ℝ) → (Fin n → ℝ)

/-- The surface (boundary) measure on $\partial \Omega$ for a domain $\Omega \subseteq \mathbb{R}^n$,
provided abstractly as an opaque measure. -/
opaque surfaceMeasure (n : ℕ) (Ω : Set (Fin n → ℝ)) : Measure (Fin n → ℝ)

/-- The outward normal derivative $\partial_\nu w(x) = \nabla w(x) \cdot \nu(x)$ at a boundary
point $x$, where $\nu$ is the outward unit normal. -/
def NormalDerivative (n : ℕ) (w : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ w x (outwardUnitNormal n x)

/-- The boundary energy integral $\int_{\partial \Omega} w(x) \, \partial_\nu w(x) \, dS$
arising from Green's first identity. -/
def boundaryEnergyIntegral {n : ℕ} (w : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : ℝ :=
  ∫ x in frontier Ω, w x * NormalDerivative n w x ∂(surfaceMeasure n Ω)

/-- Uniqueness for Poisson's equation with Robin boundary conditions $\partial_\nu u + \alpha u = g$
($\alpha > 0$): two solutions $u, v$ of $\Delta u = f = \Delta v$ on a bounded connected open set
$\Omega$ that satisfy the same Robin condition agree on $\overline{\Omega}$. -/
noncomputable def sphericalMean {n : ℕ} (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then u x
  else ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
    u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)

/-- The "spherical-average" function $r \mapsto \fint_{S^{n-1}} u(x + r\omega) \, d\sigma(\omega)$,
i.e. `sphericalMean u x r` but without the special-case branch at $r = 0$. -/
noncomputable def sphericalAvgFun {n : ℕ} (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ → ℝ :=
  fun r => ⨍ ω in Metric.sphere (0 : Fin n → ℝ) 1,
    u (x + r • ω) ∂Measure.hausdorffMeasure (↑(n - 1) : ℝ)

/-- Spherical mean-value property for harmonic functions: for $u$ harmonic on $B(x, R)$ and any
$r \in (0, R]$, the spherical mean satisfies `sphericalMean u x r = u(x)`. -/
def HasVolumeMVP {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : Prop :=
  ContinuousOn u Ω ∧
  ∀ (x : Fin n → ℝ) (R : ℝ), x ∈ Ω → 0 < R → Metric.closedBall x R ⊆ Ω →
    u x = ⨍ y in Metric.ball x R, u y

end CM7
end
