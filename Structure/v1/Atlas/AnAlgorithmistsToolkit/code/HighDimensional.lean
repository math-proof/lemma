/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HighDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Convex.Body
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.HighDimensional
public section

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
