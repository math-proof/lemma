/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.FredholmAlternative
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Abbrev.v1.Atlas.IntroductionToFunctionalAnalysis.code.SpectralTheory
open Function Set Filter Bornology Metric Pointwise Topology


namespace SpectralTheory

section AdjointOperator

variable {𝕜 : Type*} [RCLike 𝕜]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The $k$-th orthonormal sine basis function on $[0,1]$:
$u_k(x) = \sqrt{2} \sin(k\pi x)$.
These form an orthonormal eigenbasis of the Green's operator with Dirichlet
boundary conditions on the unit interval. -/
noncomputable def sineBasisFun (k : ℕ+) : ℝ → ℝ :=
  fun x => Real.sqrt 2 * Real.sin (↑k * Real.pi * x)

/-- The $k$-th eigenvalue of the Green's operator on $[0,1]$ with Dirichlet
boundary conditions: $\lambda_k = \dfrac{1}{k^2 \pi^2}$. -/
noncomputable def greensEigenvalue (k : ℕ+) : ℝ := 1 / ((k : ℝ) ^ 2 * Real.pi ^ 2)

/-- The square root of the $k$-th eigenvalue of the Green's operator,
$\sqrt{\lambda_k} = \dfrac{1}{k\pi}$. This is the $k$-th eigenvalue of $A^{1/2}$. -/
noncomputable def greensEigenvalueSqrt (k : ℕ+) : ℝ := 1 / ((k : ℝ) * Real.pi)

/-- The square root $A^{1/2}$ of the Green's operator, defined via its action on the
orthonormal eigenbasis $\{b_k\}$: if $f = \sum_k c_k\, b_k$ where
$c_k = \langle b_k, f\rangle$, then
$A^{1/2} f = \sum_k \frac{1}{k\pi}\, c_k\, b_k$. -/
noncomputable def greensOperatorSqrt (b : HilbertBasis ℕ+ ℝ L2UnitInterval) :
    L2UnitInterval → L2UnitInterval :=
  fun f => ∑' (k : ℕ+), (greensEigenvalueSqrt k * inner (𝕜 := ℝ) (b k) f) • b k

/-- The Green's kernel for the Dirichlet Laplacian on $[0,1]$:
$G(x,t) = \min(x,t)\,(1 - \max(x,t))$.
The Green's operator $f \mapsto \int_0^1 G(x,t) f(t)\,dt$ is the inverse of
$-\frac{d^2}{dx^2}$ subject to $u(0)=u(1)=0$. -/
noncomputable def greensKernel (x t : ℝ) : ℝ :=
  min x t * (1 - max x t)

end AdjointOperator
end SpectralTheory
