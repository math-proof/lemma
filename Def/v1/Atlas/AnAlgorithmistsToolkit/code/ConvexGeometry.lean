/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/ConvexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.PolarBody
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.PolarBody
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Set
open scoped Pointwise


namespace ConvexGeometry

def IsConvexBody {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (C : Set E) : Prop :=
  Convex ℝ C ∧ IsCompact C ∧ (interior C).Nonempty

end ConvexGeometry
