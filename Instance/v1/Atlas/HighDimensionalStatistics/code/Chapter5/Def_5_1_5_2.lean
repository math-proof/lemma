/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Def_5_1_5_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Def_5_1_5_2.Part2
open MeasureTheory


noncomputable section

namespace Minimax

/-- The identity map is an estimator, so `Estimator d` is nonempty. -/
instance {d : ℕ} : Nonempty (Estimator d) := ⟨id⟩

end Minimax
end
