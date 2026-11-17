/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_53_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Structure.v1.Atlas.TensorCategories.code.Theorem_1_53_1

@[expose] public section

set_option maxHeartbeats 400000
set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u v w


section CartanMatrix

variable {k : Type w} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pivotal (categorical) dimension of `V`: the left quantum trace of the pivotal
isomorphism `V ≅ V**`. -/
noncomputable def pivotalDim (u : PivotalStructureData C) (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  leftQuantumTrace' C (u.pivotalIso V).hom

end CartanMatrix
