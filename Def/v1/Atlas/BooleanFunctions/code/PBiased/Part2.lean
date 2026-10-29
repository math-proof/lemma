/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/PBiased.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Instance.v1.Atlas.BooleanFunctions.code.PBiased
open scoped NNReal
open MeasureTheory Measure PMF


namespace BooleanFourier

noncomputable def pBiasedMeasure (n : ℕ) (p : NNReal) (hp : p ≤ 1) :
    Measure (Fin n → Bool) :=
  Measure.pi (fun _ => pBiasedBit p hp)

end BooleanFourier
