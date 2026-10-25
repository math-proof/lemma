/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter11/AdvancedResults.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.FourierMultiplier
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props.Part3
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter11.AdvancedResults
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap FourierTransform Laplacian BigOperators Pointwise

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

namespace Chapter11

variable {n : ℕ}

/-- Evaluate a complex multivariate polynomial at a point of `ℝⁿ` (viewed via the
`WithLp` equivalence). -/
def evalPolyAtRn (n : ℕ) (P : MvPolynomial (Fin n) ℂ) (ξ : Rn n) : ℂ :=
  MvPolynomial.aeval (fun i => (((WithLp.equiv 2 (Fin n → ℝ)) ξ) i : ℂ)) P

/-- Embed `ℝⁿ` into `ℝⁿ⁺¹` by setting the last coordinate to zero. -/
def embedHyperplane (n : ℕ) (x : Rn n) : Rn (n + 1) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm
    (fun i : Fin (n + 1) =>
      if h : (i : ℕ) < n then (WithLp.equiv 2 (Fin n → ℝ) x) ⟨i, h⟩ else 0)

/-- Lift a point `ξ' ∈ ℝⁿ` to `ℝⁿ⁺¹` by appending `t` as the last coordinate. -/
def liftPoint (n : ℕ) (ξ' : Rn n) (t : ℝ) : Rn (n + 1) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm
    (fun i : Fin (n + 1) =>
      if h : (i : ℕ) < n
      then (WithLp.equiv 2 (Fin n → ℝ) ξ') ⟨i, h⟩
      else t)

/-- Trace along the last coordinate: integrate `f : ℝⁿ⁺¹ → ℂ` over the line
`{(ξ', t) : t ∈ ℝ}`. -/
def fourierTrace (n : ℕ) (f : Rn (n + 1) → ℂ) : Rn n → ℂ :=
  fun ξ' => ∫ t : ℝ, f (liftPoint n ξ' t)

/-- The `i`-th standard basis vector in `ℝⁿ`. -/
def stdBasisVec (n : ℕ) (i : Fin n) : Rn n := EuclideanSpace.single i 1

/-- The `k`-fold iterated directional derivative in direction `v` on tempered
distributions. -/
def iterLineDeriv {n : ℕ} (v : Rn n) : ℕ → 𝓢'(Rn n, ℂ) → 𝓢'(Rn n, ℂ)
  | 0 => id
  | k + 1 => fun u => LineDeriv.lineDerivOp v (iterLineDeriv v k u)

/-- The multi-derivative `∂^α = ∂_1^{α₁} ⋯ ∂_n^{αₙ}` of a tempered distribution. -/
def iterMultiDeriv (n : ℕ) (α : Fin n → ℕ) (u : 𝓢'(Rn n, ℂ)) : 𝓢'(Rn n, ℂ) :=
  (Finset.univ.toList.map (fun i => iterLineDeriv (stdBasisVec n i) (α i))).foldl
    (fun acc f => f acc) u

/-- A tempered distribution is `L²`-represented if it acts on Schwartz functions
by pairing with an `L²` function. -/
def IsL2Represented {n : ℕ} (u : 𝓢'(Rn n, ℂ)) : Prop :=
  ∃ f : Rn n → ℂ,
    AEStronglyMeasurable f volume ∧
    Integrable (fun x : Rn n => ‖f x‖ ^ 2) volume ∧
    (∀ φ : 𝓢(Rn n, ℂ), u φ = ∫ x, f x • φ x)

/-- The support of a tempered distribution: the set of points such that no
compactly-supported smooth cutoff vanishes the distribution near them. -/
def DistribSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [(MeasureTheory.volume : Measure E).HasTemperateGrowth]
    (u : 𝓢'(E, ℂ)) : Set E :=
  {x : E | ∀ (φ : E → ℂ), ContDiff ℝ ⊤ φ → HasCompactSupport φ → φ x ≠ 0 →
    ¬(∀ ψ : 𝓢(E, ℂ), (∀ y, y ∉ Function.support φ → ψ y = 0) → u ψ = 0)}

/-- Iterated directional derivative on Schwartz functions in direction `v`. -/
def iterLineDerivSchwartz {n : ℕ} (v : Rn n) : ℕ → 𝓢(Rn n, ℂ) → 𝓢(Rn n, ℂ)
  | 0 => id
  | k + 1 => fun φ => LineDeriv.lineDerivOp v (iterLineDerivSchwartz v k φ)

/-- The multi-derivative `∂^α` on Schwartz functions. -/
def iterMultiDerivSchwartz (n : ℕ) (α : Fin n → ℕ) (φ : 𝓢(Rn n, ℂ)) : 𝓢(Rn n, ℂ) :=
  (Finset.univ.toList.map (fun i => iterLineDerivSchwartz (stdBasisVec n i) (α i))).foldl
    (fun acc f => f acc) φ

/-- Membership in the Sobolev space `H^s`: the Fourier transform is represented by
a function `f` with `(1 + |ξ|²)^s |f|²` integrable. -/
def MemSobolevSpace (n : ℕ) (s : ℝ) (u : 𝓢'(Rn n, ℂ)) : Prop :=
  ∃ f : Rn n → ℂ,
    AEStronglyMeasurable f volume ∧
    (∀ φ : 𝓢(Rn n, ℂ), (𝓕 u) φ = ∫ x, f x • φ x) ∧
    Integrable (fun ξ : Rn n =>
      ((1 + ‖ξ‖ ^ 2 : ℝ) ^ s : ℝ) * ‖f ξ‖ ^ 2) volume

end Chapter11
end
