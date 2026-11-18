/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Structure.v1.Atlas.TensorCategories.code.IntegralsCartanMatrix

@[expose] public section
set_option maxHeartbeats 400000

set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u v w


section CartanMatrix

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The pivotal dimension of `V` with respect to the pivotal structure `u`, namely
the left quantum trace of `u.pivotalIso V` (Definition 1.38.4). -/
noncomputable def pivotalDim (u : PivotalStructureData C) (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  leftQuantumTrace' C (u.pivotalIso V).hom

end CartanMatrix
