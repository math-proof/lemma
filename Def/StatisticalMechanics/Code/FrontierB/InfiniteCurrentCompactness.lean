module
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology.Part8
public import Mathlib.MeasureTheory.Measure.Prokhorov
open Filter MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentCompactness.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

variable {E : Type*} [Countable E]


def currentCoordinateBox (K : E → ℕ) : Set (InfiniteCurrentConfig E) :=
  Set.univ.pi (fun e => Set.Iio (K e))

end StatMech.FrontierB
