/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/TSPConcentration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
set_option maxHeartbeats 400000
set_option linter.unusedVariables false


namespace RheeTalagrand

open Real MeasureTheory Set

/-- A point in the plane $\mathbb{R}^2$, represented as a function $\mathrm{Fin}\,2 \to \mathbb{R}$. -/
abbrev Point := Fin 2 → ℝ

end RheeTalagrand
