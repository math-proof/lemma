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
public import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part4
open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap

public section

noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {n : ℕ}

/-- The defining property of `Hs.witnessFunc`: pairing `𝓕 u` against a
Schwartz function recovers the integral of `⟨ξ⟩^{-s} · witnessFunc · φ`. -/
lemma Hs.witnessFunc_spec (s : ℝ) (u : Hs n s) :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u.1) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * Hs.witnessFunc n s u ξ * φ ξ :=
  u.2.choose_spec.2


end Isomorphism
end FourierInversion
end
