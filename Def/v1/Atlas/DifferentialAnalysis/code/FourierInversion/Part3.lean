/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzRepresentation
public import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
public import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzRepresentation
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.TransferInstance
public import Mathlib.Analysis.Fourier.LpSpace
public import Theorem.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part2

@[expose] public section

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap


noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {n : ℕ}

/-- Membership in the Sobolev space `H^s(ℝⁿ)`: a tempered distribution `u`
belongs to `H^s` if there exists `g ∈ L²` such that, for every Schwartz
function `φ`, `(𝓕 u)(φ) = ∫ ⟨ξ⟩^{-s} g(ξ) φ(ξ) dξ`. Equivalently, `𝓕 u`
is given by integration against the `L²` function `⟨ξ⟩^{-s} g`. -/
def MemHs (s : ℝ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ g : EuclideanSpace ℝ (Fin n) → ℂ,
    MemLp g 2 ∧
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g ξ * φ ξ

/-- The Sobolev space `H^s(ℝⁿ)` realised as the subtype of tempered
distributions satisfying `MemHs n s`. -/
def Hs (s : ℝ) : Type :=
  { u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) // MemHs n s u }

/-- The `L²` "witness" function attached to a Sobolev distribution: it is
the function `g` produced by the existential in `MemHs`. Concretely,
`𝓕 u = ⟨ξ⟩^{-s} · witnessFunc s u` as distributions. -/
def Hs.witnessFunc (s : ℝ) (u : Hs n s) : EuclideanSpace ℝ (Fin n) → ℂ :=
  u.2.choose

end Isomorphism
end FourierInversion
end
