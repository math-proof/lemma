/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Problem_5_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.InformationTheory.KullbackLeibler.Basic

@[expose] public section

open MeasureTheory InformationTheory


namespace Chapter5.Problem52

/-- Real-valued KL divergence used in Problem 5.2: `(klDiv P Q).toReal`. -/
noncomputable def klDivReal {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : ℝ :=
  (klDiv P Q).toReal

end Chapter5.Problem52
