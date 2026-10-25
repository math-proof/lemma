/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Lemma.Category.Atlas.v1.TensorCategories.code.VecInstances
import Lemma.Category.Atlas.v1.TensorCategories.code.VecPivotalConcrete
import Lemma.Category.Atlas.v1.TensorCategories.code.VecSphericalConcrete
import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
import Theorem.v1.Atlas.TensorCategories.code.DualCoherenceBridge
import Def.v1.Atlas.TensorCategories.code.VecPivotalConcrete.Part2
import Theorem.v1.Atlas.TensorCategories.code.VecSphericalConcrete
import Def.v1.Atlas.TensorCategories.code.VecPivotal
open CategoryTheory Module TensorCategories VecInstances MonoidalCategory Category

universe u

variable (k : Type u) [Field k]


section PivotalSphericalInstances

attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory

attribute [-instance] BraidedCategory.rigidCategoryOfLeftRigidCategory

attribute [-instance] RigidCategory.toRightRigidCategory

set_option maxHeartbeats 800000 in
/-- `Vec k = FGModuleCat k` is a pivotal category, with pivotal structure given by
the canonical double-dual isomorphism (Definition 1.38.2). -/
noncomputable instance : PivotalCategory (Vec k) :=
  vecPivotalCategoryInstance k

set_option maxHeartbeats 800000 in
/-- `Vec k` is a spherical category (Definition 1.39.1): the pivotal dimension of any
object equals the pivotal dimension of its dual. -/
noncomputable instance : SphericalCategory (Vec k) where
  spherical := fun V => by


    show TensorCategories.pivotalDimension (Vec k) V =
         TensorCategories.pivotalDimension (Vec k) (Vᘁ)

    change TensorCategories.leftQuantumTrace (Vec k) (PivotalCategory.pivotalIso V).hom =
           TensorCategories.leftQuantumTrace (Vec k) (PivotalCategory.pivotalIso (Vᘁ)).hom


    exact vec_spherical_condition k V

end PivotalSphericalInstances
