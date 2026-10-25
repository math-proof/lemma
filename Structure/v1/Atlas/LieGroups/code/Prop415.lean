/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Prop415.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs


noncomputable section

open scoped Manifold Topology

open MeasureTheory

structure ContinuousRepresentation (G : Type*) [Group G] [TopologicalSpace G]
    (V : Type*) [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] where
  toMonoidHom : G →* (V →L[ℂ] V)
  continuous_action : Continuous (fun p : G × V => (toMonoidHom p.1) p.2)

end
