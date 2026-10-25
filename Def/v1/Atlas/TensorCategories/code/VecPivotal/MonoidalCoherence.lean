/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotal/MonoidalCoherence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open CategoryTheory MonoidalCategory Module Category

universe u


noncomputable section

variable (k : Type u) [Field k]

section MonoidalCoherence

attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory

attribute [-instance] BraidedCategory.rigidCategoryOfLeftRigidCategory

attribute [-instance] RigidCategory.toRightRigidCategory

/-- The canonical linear equivalence `(V ⊗ W)* ≃ₗ[k] W* ⊗ V*` for finite-dimensional
free `k`-modules, obtained by chaining the tensor-hom adjunction with the swap. -/
def dualTensorSwapEquiv (V W : Type u)
    [AddCommGroup V] [Module k V] [Module.Free k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Free k W] [Module.Finite k W] :
    Module.Dual k (TensorProduct k V W) ≃ₗ[k]
      TensorProduct k (Module.Dual k W) (Module.Dual k V) :=
  ((TensorProduct.lift.equiv (RingHom.id k) V W k).symm).trans <|
  ((dualTensorHomEquiv k V (Module.Dual k W)).symm).trans <|
  (TensorProduct.comm k (Module.Dual k V) (Module.Dual k W))

/-- The canonical tensor-coherence isomorphism `(V*)* ⊗ (W*)* ≅ ((V ⊗ W)*)*` in
`FGModuleCat k`, needed to assemble a monoidal pivotal structure. -/
def vecMonoidalDoubleDualIso (V : FGModuleCat k) : V ≅ (Vᘁ)ᘁ :=
  (Module.evalEquiv k V).toFGModuleCatIso

end MonoidalCoherence
end
