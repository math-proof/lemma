/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.ExponentialBounds
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13
open MeasureTheory InformationTheory


noncomputable section

namespace GaussianSequenceModel

/-- `Estimator d` is nonempty (witnessed by the identity). -/
instance {d : ℕ} : Nonempty (Estimator d) := ⟨id⟩

end GaussianSequenceModel
end
