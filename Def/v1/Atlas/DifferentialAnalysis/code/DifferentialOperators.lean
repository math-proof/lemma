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
open scoped SchwartzMap
open TemperedDistribution MvPolynomial


noncomputable section

namespace DifferentialOperators

variable (n : ℕ)

/-- The **principal symbol** of a polynomial `P` of (assumed) order `m`:
the degree-`m` homogeneous component of `P`. -/
def principalSymbol (m : ℕ) (P : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  homogeneousComponent m P

/-- A polynomial `P(ξ)` (of order `m`) is **elliptic** if its principal
symbol `P_m(ξ)` does not vanish for any nonzero real vector `ξ ∈ ℝⁿ`.
(See Melrose, Definition 11.11.) -/
def IsElliptic (m : ℕ) (P : MvPolynomial (Fin n) ℂ) : Prop :=
  ∀ ξ : Fin n → ℝ, ξ ≠ 0 →
    MvPolynomial.eval (fun i => (ξ i : ℂ)) (principalSymbol n m P) ≠ 0

/-- The **Fourier symbol** `P(2πiξ)` of the differential operator `P(D)`,
viewed as a function `ℝⁿ → ℂ`. -/
def polySymbol (P : MvPolynomial (Fin n) ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun ξ => MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ)) P

/-- The **constant-coefficient differential operator** `P(D)` acting on
tempered distributions, defined as the Fourier multiplier with symbol
`P(2πiξ)`. -/
def constCoeffDiffOp (P : MvPolynomial (Fin n) ℂ) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  TemperedDistribution.fourierMultiplierCLM ℂ (polySymbol n P)

/-- A tempered distribution `E` is a **fundamental solution** of `P(D)`
if `P(D) E = δ₀`. -/
def IsTemperedFundamentalSolution (P : MvPolynomial (Fin n) ℂ)
    (E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  constCoeffDiffOp n P E = TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))


/-- **Theorem 11.4 (Melrose).** Every nonzero constant-coefficient differential
operator `P(D)` admits a tempered fundamental solution. -/

section SingularSupport

variable {n : ℕ}

/-- A tempered distribution `u` is **smooth near** a point `x₀` if there
exists an open neighbourhood `U` of `x₀` on which `u` is represented by a
smooth function (under pairing with Schwartz functions supported in `U`). -/
def isSmoothNear (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (x₀ : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x₀ ∈ U ∧
    ∃ f : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) →
        u φ = ∫ y, φ y • f y

/-- The **singular support** of `u`: the set of points `x₀` near which
`u` fails to be smooth. -/
def singularSupport (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x₀ | ¬ isSmoothNear u x₀}

/-- `u` **vanishes on** the set `U` if it sends every test function
supported in `U` to zero. -/
def vanishesOn (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) → u φ = 0

end SingularSupport

section OperatorProperties

variable {n : ℕ}

/-- A tempered distribution `F` is a **parametrix** for `P(D)` if
`P(D) F - δ₀` has empty singular support, i.e. it is smooth everywhere.
(See Melrose, Definition 11.8.) -/
def IsParametrix (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  singularSupport
    (constCoeffDiffOp n P F - TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))) = ∅

/-- `P(D)` is **hypoelliptic** if it admits a parametrix `F` whose
singular support is contained in `{0}`. -/
def IsHypoelliptic (P : MvPolynomial (Fin n) ℂ) : Prop :=
  ∃ (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
    IsParametrix P F ∧
    singularSupport F ⊆ {(0 : EuclideanSpace ℝ (Fin n))}

end OperatorProperties
end DifferentialOperators
end
