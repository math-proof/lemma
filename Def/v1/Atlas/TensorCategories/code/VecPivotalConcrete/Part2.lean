/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotalConcrete.lean -/

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
import Lemma.Category.Atlas.v1.TensorCategories.code.VecDualMapBridge
import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
import Theorem.v1.Atlas.TensorCategories.code.VecDualMapBridge
import Theorem.v1.Atlas.TensorCategories.code.VecPivotalConcrete
open CategoryTheory MonoidalCategory Module Category TensorCategories

universe u


noncomputable section

variable (k : Type u) [Field k]

section FixDiamond

attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory

attribute [-instance] BraidedCategory.rigidCategoryOfLeftRigidCategory

attribute [-instance] RigidCategory.toRightRigidCategory

set_option maxHeartbeats 800000 in
/-- `FGModuleCat k` is a pivotal category, with pivotal structure given by the canonical
double-dual evaluation isomorphism. This corresponds to Definitions 1.38.1–1.38.2. -/
@[reducible]
noncomputable def vecPivotalCategoryInstance :
    @PivotalCategory (FGModuleCat k) _ _ _ where
  pivotalIso := vecDoubleDualIsoConcrete k
  tensorCoherenceIso := vecTensorCoherenceIsoConcrete k
  naturality := fun f => vecDoubleDualIsoConcrete_naturality k f
  monoidality := fun V W => vecDoubleDualIsoConcrete_monoidality k V W
  dimUnit := vecDoubleDualIsoConcrete_dimUnit k

end FixDiamond
end
