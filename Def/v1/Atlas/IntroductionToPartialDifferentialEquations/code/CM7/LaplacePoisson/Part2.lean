/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplacePoisson.Part2
open Real Set MeasureTheory Filter


noncomputable section

namespace LaplacePoisson

/-- **Weyl's lemma**: a function whose integral against $\Delta\psi$ vanishes for
every test function $\psi$ supported in $\Omega$ is necessarily smooth and harmonic
on $\Omega$. -/
noncomputable def sphereIntegralLP {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ σ in frontier (Metric.ball x ε), f σ ∂(surfaceMeasure (Metric.ball x ε))

/-- Green's representation formula derived from the corrector identity: combining the
$\Phi$-version of the representation formula with the harmonic-corrector identity
$\varphi = \Phi - G$ yields the clean Green-function formula
$u(x) = \int_\Omega f \cdot G(x, \cdot) + \int_{\partial \Omega} g \cdot \partial_\nu G(x, \cdot)$. -/
def laplacianE {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)

/-- A function $u$ on `EuclideanSpace ℝ (Fin n)` is harmonic on $\Omega$ iff
$\Delta u = 0$ on $\Omega$. -/
def IsHarmonicE {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ Ω, laplacianE u x = 0

/-- Opaque outward unit normal on $\partial\Omega$, valued in `EuclideanSpace ℝ (Fin n)`. -/
opaque outwardUnitNormalE {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)

/-- Explicit form of the outward unit normal on a ball in $\mathbb{R}^3$:
$\nu(\sigma) = (\sigma - p)/R$ for $\sigma$ on the sphere of radius $R$ about $p$. -/
def normalDerivE {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (σ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, fderiv ℝ f σ (EuclideanSpace.single i 1) * outwardUnitNormalE Ω σ i

/-- Surface integral $\int_{\partial \Omega} f\,dS$ on `EuclideanSpace`. -/
def surfaceIntegralE {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ σ in frontier Ω, f σ ∂(surfaceMeasureE Ω)

end LaplacePoisson
end
