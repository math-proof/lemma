module
public import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
public import Theorem.Category.Atlas.v1.TensorCategories.code.GradedVec
public import Mathlib.GroupTheory.GroupAction.Basic
public import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part3
set_option maxHeartbeats 800000
open CategoryTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u v


section MonoidalFunctorComposition

/-- The identity homomorphism together with the trivial 2-cochain provides identity
monoidal functor data on `(G, ω)`. -/
theorem isMonoidalFunctorData_id (G : Type u) [Group G] (A : Type v) [CommGroup A]
    (ω : Cochain3' G A) :
    IsMonoidalFunctorData G G A ω ω (MonoidHom.id G) (fun _ _ => 1) := by
  intro g h l
  simp [MonoidHom.id_apply]

end MonoidalFunctorComposition
