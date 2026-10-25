/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HighDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.Body
open MeasureTheory

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped NNReal


namespace HighDimensional

def IsCLipschitz {α : Type*} {β : Type*} [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
    (c : ℝ) (f : α → β) : Prop :=
  ∀ u v : α, ‖f u - f v‖ ≤ c * ‖u - v‖

end HighDimensional
