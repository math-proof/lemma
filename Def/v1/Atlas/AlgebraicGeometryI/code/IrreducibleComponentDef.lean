/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/IrreducibleComponentDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Irreducible


section IrreducibleComponent

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- Irreducible component (Def 8, Lec 3): a subset `s ⊆ X` is an irreducible component
if it is a maximal irreducible closed subset of `X`. -/
def IsIrreducibleComponentOf (s : Set X) : Prop :=
  s ∈ irreducibleComponents X

end IrreducibleComponent
