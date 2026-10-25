/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Theorem.v1.Atlas.DifferentialAnalysis.code.DistributionSupport
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DistributionSupport
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzTranslateContinuity
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzTranslateContinuity
import Instance.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators
open scoped SchwartzMap
open TemperedDistribution MvPolynomial


noncomputable section

namespace DifferentialOperators

variable (n : ℕ)

section OperatorProperties

variable {n : ℕ}

namespace SmoothZeroAtInfty

variable {n : ℕ}

/-- The **Laplacian polynomial** `P(X) = Σⱼ Xⱼ²`, whose associated
constant-coefficient differential operator is the Laplacian
`Δ = Σⱼ ∂ⱼ²` (up to the usual `(2πi)²` factor coming from the Fourier
normalisation). -/
def laplacianPoly : MvPolynomial (Fin n) ℂ :=
  ∑ j : Fin n, MvPolynomial.X j ^ 2

/-- The **Laplacian** as a continuous linear operator on tempered
distributions, defined via the constant-coefficient differential operator
machinery applied to `laplacianPoly`. -/
def laplacianOp :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  constCoeffDiffOp n (laplacianPoly)

end PoissonEquation

end DifferentialOperators

namespace DifferentialOperators

/-- The **classical Laplacian relation** between smooth functions
`f, g : ℝⁿ → ℂ`: `g(x) = -Σⱼ ∂_j² f(x)` for every `x`. (The convention sign
comes from the Fourier multiplier `-|2πξ|²` of `Δ`.) -/
def IsLaplacianOf_DO (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    g x = -∑ j : Fin n,
      (iteratedFDeriv ℝ 2 f x) (fun _ => EuclideanSpace.single j (1 : ℝ))


/-- **Integration-by-parts formula for the Laplacian on a smooth
representative.** If a tempered distribution `u_td` is represented by a
smooth function `u` vanishing at infinity (with all derivatives), then for
every Schwartz test function `φ`, applying the distributional Laplacian
equals the integral of `φ` against the classical Laplacian `-Σⱼ ∂_j² u`. -/

end DifferentialOperators

open SchwartzMap MeasureTheory Distribution

open scoped Topology

namespace Distribution

section SingularSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [BorelSpace E]

/-- A tempered distribution `u` is **smooth on** the set `s` if there
is a globally smooth `g : E → ℂ` such that `u φ = ∫ φ g` for every
Schwartz function `φ` with `tsupport φ ⊆ s`. -/
def IsSmoothOn (u : 𝓢'(E, ℂ)) (s : Set E) : Prop :=
  ∃ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧
    ∀ φ : 𝓢(E, ℂ), tsupport φ ⊆ s → u φ = ∫ x, φ x • g x

/-- The **singular support** of `u`: complement of the union of all open
sets on which `u` is represented by a smooth function. -/
def singularSupport (u : 𝓢'(E, ℂ)) : Set E :=
  (⋃₀ {s | IsSmoothOn u s ∧ IsOpen s})ᶜ

end SingularSupport

end Distribution

end

noncomputable section

open scoped SchwartzMap Topology

open Distribution SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace DifferentialOperators

/-- A tempered distribution `v` has **compact distributional support** if
its `dsupport` is a compact subset of the underlying space. -/
def HasCompactDsupport {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v : 𝓢'(E, F)) : Prop :=
  IsCompact (dsupport v)

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Multiplying a Schwartz function by a smooth compactly-supported real
cutoff `χ` produces another Schwartz function `χ · f`. -/
noncomputable def cutoffMul (χ : E → ℝ) (hχcs : HasCompactSupport χ)
    (hχcd : ContDiff ℝ ⊤ χ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  (hχcs.smul_right (f' := ⇑f)).toSchwartzMap
    ((hχcd.of_le le_top).smul f.smooth')

end DifferentialOperators
end
