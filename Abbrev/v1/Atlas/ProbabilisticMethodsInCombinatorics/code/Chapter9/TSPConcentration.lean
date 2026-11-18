/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/TSPConcentration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
public import Theorem.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
@[expose] public section
set_option maxHeartbeats 400000
set_option linter.unusedVariables false


namespace RheeTalagrand

open Real MeasureTheory Set

/-- A point in the plane $\mathbb{R}^2$, represented as a function $\mathrm{Fin}\,2 \to \mathbb{R}$. -/
abbrev Point := Fin 2 → ℝ

end RheeTalagrand
