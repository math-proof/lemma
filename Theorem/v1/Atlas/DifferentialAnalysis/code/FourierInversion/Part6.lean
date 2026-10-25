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
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part6
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


/-- The norm on `H^s` is defined to equal the `L²` norm of the witness:
`‖u‖_{H^s} = ‖witnessL2 u‖_{L²}`. -/
theorem Hs.norm_witnessL2 (s : ℝ) (u : Hs n s) :
    ‖u‖ = ‖Hs.witnessL2 n s u‖ := rfl


/-- The witness map `Hs n s → L²` is additive. -/
theorem Hs.witnessL2_add (s : ℝ) (u v : Hs n s) :
    Hs.witnessL2 n s (u + v) = Hs.witnessL2 n s u + Hs.witnessL2 n s v := by
  show (Hs.equivLp n s) (u + v) = (Hs.equivLp n s) u + (Hs.equivLp n s) v
  simp [show (u + v : Hs n s) = (Hs.equivLp n s).symm
    ((Hs.equivLp n s) u + (Hs.equivLp n s) v) from rfl]


/-- The witness map `Hs n s → L²` is `ℂ`-linear. -/
theorem Hs.witnessL2_smul (s : ℝ) (c : ℂ) (u : Hs n s) :
    Hs.witnessL2 n s (c • u) = c • Hs.witnessL2 n s u := by
  show (Hs.equivLp n s) (c • u) = c • (Hs.equivLp n s) u
  simp [show (c • u : Hs n s) = (Hs.equivLp n s).symm
    (c • (Hs.equivLp n s) u) from rfl]

end Isomorphism
end FourierInversion
end
