/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzRepresentation
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzRepresentation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.Fourier.LpSpace
import Theorem.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part6
open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap


noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {n : ℕ}

attribute [instance] Hs.instNormedAddCommGroup


attribute [instance] Hs.instInnerProductSpace


/-- The "Fourier-weight" linear isometric equivalence between `H^s(ℝⁿ)` and
`L²(ℝⁿ; ℂ)` sending each `u` to its `L²` witness `⟨ξ⟩^s · 𝓕u`. This is the
fundamental Hilbert-space identification underlying the definition of
`H^s`. -/
noncomputable def fourierWeightEquiv (s : ℝ) :
    Hs n s ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  LinearIsometryEquiv.ofSurjective
    ({ toLinearMap :=
        { toFun := Hs.witnessL2 n s
          map_add' := Hs.witnessL2_add n s
          map_smul' := Hs.witnessL2_smul n s }
       norm_map' := fun u => (Hs.norm_witnessL2 n s u).symm } : Hs n s →ₗᵢ[ℂ]
         MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (fun f => ⟨Hs.fromL2 n s f, Hs.fromL2_witnessL2 n s f⟩)

/-- The Sobolev duality identification: `H^{-s} ≃ (H^s)'` as anti-linear
isometric equivalences, obtained by composing the two Fourier-weight
isometries with the Riesz representation `H^s ≃ (H^s)'`. This is part of
Proposition 9.8 of Melrose. -/
noncomputable def dualIdentification (s : ℝ) :
    Hs n (-s) ≃ₗᵢ⋆[ℂ] (Hs n s →L[ℂ] ℂ) :=
  ((fourierWeightEquiv n (-s)).trans (fourierWeightEquiv n s).symm).trans
    (InnerProductSpace.toDual ℂ (Hs n s))

end Isomorphism
end FourierInversion
end
