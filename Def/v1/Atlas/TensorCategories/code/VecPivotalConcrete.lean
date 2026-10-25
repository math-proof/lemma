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
open CategoryTheory MonoidalCategory Module Category TensorCategories

universe u


noncomputable section

variable (k : Type u) [Field k]

section FixDiamond

attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory

attribute [-instance] BraidedCategory.rigidCategoryOfLeftRigidCategory

attribute [-instance] RigidCategory.toRightRigidCategory

/-- The concrete double-dual isomorphism `V ≅ (V*)*` in `FGModuleCat k`, obtained
from the canonical evaluation equivalence on finite-dimensional vector spaces. -/
noncomputable def vecDoubleDualIsoConcrete (V : FGModuleCat k) : V ≅ (Vᘁ)ᘁ :=
  (Module.evalEquiv k V).toFGModuleCatIso

/-- The tensor-coherence isomorphism `(V*)* ⊗ (W*)* ≅ ((V ⊗ W)*)*` in `FGModuleCat k`,
built by combining the double-dual isomorphisms on the factors with the one on the tensor. -/
noncomputable def vecTensorCoherenceIsoConcrete (V W : FGModuleCat k) :
    (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : FGModuleCat k)ᘁ : FGModuleCat k)ᘁ :=
  (MonoidalCategory.tensorIso
    (vecDoubleDualIsoConcrete k V).symm
    (vecDoubleDualIsoConcrete k W).symm) ≪≫
  (vecDoubleDualIsoConcrete k (V ⊗ W))

end FixDiamond
end
