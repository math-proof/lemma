/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/ConvexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.PolarBody
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.PolarBody
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Basic
open Set
open scoped Pointwise


namespace ConvexGeometry

def IsConvexBody {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (C : Set E) : Prop :=
  Convex ℝ C ∧ IsCompact C ∧ (interior C).Nonempty

end ConvexGeometry
