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
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.HighDimensional
open MeasureTheory

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped NNReal


namespace HighDimensional

structure IsDEmbedding {X : Type*} [MetricSpace X] [Fintype X] {k : ℕ}
    (D : ℝ) (f : X → EuclideanSpace ℝ (Fin k)) : Prop where
  one_lipschitz : ∀ x y : X, ‖f x - f y‖ ≤ dist x y
  distortion_bound : ∀ x y : X, dist x y ≤ D * ‖f x - f y‖


end HighDimensional
