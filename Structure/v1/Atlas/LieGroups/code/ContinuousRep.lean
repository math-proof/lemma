/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ContinuousRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Sequences


noncomputable section

open scoped ComplexOrder

structure ContinuousRep
    (G : Type*) [Group G] [TopologicalSpace G]
    (V : Type*) [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] where
  toMonoidHom : G →* (V →L[ℂ] V)
  continuous_action : Continuous (fun p : G × V => (toMonoidHom p.1) p.2)

end
