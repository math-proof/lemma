/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Thm_5_11
open MeasureTheory InformationTheory Real Finset


noncomputable section

namespace MinimaxLowerBound

/-- The identity map is an estimator. -/
instance {d : ℕ} : Nonempty (Estimator d) := ⟨id⟩

/-- The identity is a measurable estimator, providing nonemptiness of the
subtype of measurable estimators used in `minimaxRisk`. -/
instance {d : ℕ} : Nonempty { f : Estimator d // Measurable f } :=
  ⟨⟨id, measurable_id⟩⟩

end MinimaxLowerBound
end
