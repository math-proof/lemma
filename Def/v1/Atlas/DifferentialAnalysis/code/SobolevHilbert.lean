/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HilbertSpace
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Class.v1.Atlas.DifferentialAnalysis.code.HilbertSpace
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Affine.MazurUlam


noncomputable section

open MeasureTheory

namespace SobolevHilbert

/-- The Japanese bracket `⟨ξ⟩ := sqrt(1 + ‖ξ‖²)` used as a smooth comparison weight. -/
def japaneseBracket {E : Type*} [NormedAddCommGroup E] (ξ : E) : ℝ :=
  Real.sqrt (1 + ‖ξ‖ ^ 2)

/-- The Sobolev weight `(1 + ‖ξ‖²)^m`, the symbol used to define `H^m` via the Fourier transform. -/
def sobolevWeight {E : Type*} [NormedAddCommGroup E] (m : ℝ) (ξ : E) : ℝ :=
  ((1 : ℝ) + ‖ξ‖ ^ 2) ^ m


end SobolevHilbert
end
