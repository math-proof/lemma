/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/GaugeAction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.Topology.VectorBundle.Basic
public import Abbrev.v1.Atlas.GeometryOfManifolds.code.GaugeAction

@[expose] public section

set_option autoImplicit false


noncomputable section

namespace SWGaugeGroup

variable {M : Type*} [TopologicalSpace M]

/-- The embedding $S^1 \hookrightarrow \mathcal{G}$ as constant maps; its image is the central stabilizer of reducible solutions. -/
def constEmb : Circle →* SWGaugeGroup M where
  toFun z := ContinuousMap.const M z
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- A gauge transformation $f \in \mathcal{G}$ is constant if $f \equiv z \in S^1$ everywhere. -/
def IsConstant (f : SWGaugeGroup M) : Prop :=
  ∃ z : Circle, f = constEmb z

end SWGaugeGroup
end
