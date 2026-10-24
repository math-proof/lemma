/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidMonoidalDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Functor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits MonoidalOpposite Opposite

universe v u

namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]


/-- Definition 1.10.1 (alias): an object `X` has a right dual. -/
abbrev Definition_1_10_1 (X : C) := HasRightDual X

/-- Definition 1.10.1 (named right dual): an object `X` has a right dual. -/
abbrev Definition_1_10_1_RightDual (X : C) := HasRightDual X

/-- Companion to Definition 1.10.1: an object `X` has a left dual. -/
abbrev def_1_10_1_LeftDual (X : C) := HasLeftDual X


/-- Definition 1.10.2: an object `X` has a left dual. -/
abbrev Definition_1_10_2 (X : C) := HasLeftDual X


section Prop_1_10_4

/-- Proposition 1.10.4 (right): Any two right duals `Y₁`, `Y₂` of `X` are canonically
isomorphic. -/
def prop_1_10_4_right_iso {X Y₁ Y₂ : C}
    (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) : Y₁ ≅ Y₂ :=
  rightDualIso p₁ p₂

/-- Proposition 1.10.4 (left): Any two left duals `X₁`, `X₂` of `Y` are canonically
isomorphic. -/
def prop_1_10_4_left_iso {X₁ X₂ Y : C}
    (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) : X₁ ≅ X₂ :=
  leftDualIso p₁ p₂

/-- Proposition 1.10.9 (i, first equivalence): `Hom(U ⊗ V, W) ≃ Hom(U, W ⊗ V')` for an
exact pairing `(V, V')`. -/
def prop_1_10_9_right (U V V' W : C) [ExactPairing V V'] :
    (U ⊗ V ⟶ W) ≃ (U ⟶ W ⊗ V') :=
  tensorRightHomEquiv U V V' W

/-- Proposition 1.10.9 (i, second equivalence): `Hom(V' ⊗ U, W) ≃ Hom(U, V ⊗ W)` for an
exact pairing `(V, V')`. -/
def prop_1_10_9_left (U V V' W : C) [ExactPairing V V'] :
    (V' ⊗ U ⟶ W) ≃ (U ⟶ V ⊗ W) :=
  tensorLeftHomEquiv U V V' W

/-- Proposition 1.10.9 adjunction (i): `(- ⊗ V) ⊣ (- ⊗ V')` for an exact pairing
`(V, V')`. -/
def prop_1_10_9_right_adj (V V' : C) [ExactPairing V V'] :
    tensorRight V ⊣ tensorRight V' :=
  tensorRightAdjunction V V'

/-- Proposition 1.10.9 adjunction (i, left): `(V' ⊗ -) ⊣ (V ⊗ -)` for an exact pairing
`(V, V')`. -/
def prop_1_10_9_left_adj (V V' : C) [ExactPairing V V'] :
    tensorLeft V' ⊣ tensorLeft V :=
  tensorLeftAdjunction V V'

/-- Proposition 1.10.9: For `X` with a right dual `Xᘁ`, the functor `(- ⊗ X)` is left
adjoint to `(- ⊗ Xᘁ)`. -/
def prop_1_10_9_tensorRight_adj (X : C) [HasRightDual X] :
    tensorRight X ⊣ tensorRight (Xᘁ) :=
  tensorRightAdjunction X (Xᘁ)

/-- Proposition 1.10.9: For `X` with a right dual `Xᘁ`, the functor `(Xᘁ ⊗ -)` is left
adjoint to `(X ⊗ -)`. -/
def prop_1_10_9_tensorLeft_adj (X : C) [HasRightDual X] :
    tensorLeft (Xᘁ) ⊣ tensorLeft X :=
  tensorLeftAdjunction X (Xᘁ)

/-- Proposition 1.10.9 (ii): For `X` with a left dual `ᘁX`, the functor `(- ⊗ ᘁX)` is left
adjoint to `(- ⊗ X)`. -/
def prop_1_10_9ii_tensorRight_adj (X : C) [HasLeftDual X] :
    tensorRight (ᘁX : C) ⊣ tensorRight X :=
  tensorRightAdjunction (ᘁX : C) X

/-- Proposition 1.10.9 (ii): For `X` with a left dual `ᘁX`, the functor `(X ⊗ -)` is left
adjoint to `(ᘁX ⊗ -)`. -/
def prop_1_10_9ii_tensorLeft_adj (X : C) [HasLeftDual X] :
    tensorLeft X ⊣ tensorLeft (ᘁX : C) :=
  tensorLeftAdjunction (ᘁX : C) X

end Prop_1_10_9


section Remark_1_10_10

/-- Remark 1.10.10 (representability): `Hom(V', W) ≃ Hom(𝟙, V ⊗ W)` for an exact pairing
`(V, V')`. -/
noncomputable def remark_1_10_10_representability (V V' W : C) [ExactPairing V V'] :
    (V' ⟶ W) ≃ (𝟙_ C ⟶ V ⊗ W) :=
  (Equiv.mk (fun f => (ρ_ V').hom ≫ f) (fun g => (ρ_ V').inv ≫ g)
    (fun f => by simp) (fun g => by simp)).trans (tensorLeftHomEquiv (𝟙_ C) V V' W)

/-- Remark 1.10.10: For two right duals `Y₁`, `Y₂` of `X`, the hom-functor out of them
agrees: `Hom(Y₁, W) ≃ Hom(Y₂, W)`. -/
noncomputable def remark_1_10_10_hom_equiv {X Y₁ Y₂ : C}
    (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) (W : C) :
    (Y₁ ⟶ W) ≃ (Y₂ ⟶ W) :=
  (@remark_1_10_10_representability C _ _ X Y₁ W p₁).trans
    (@remark_1_10_10_representability C _ _ X Y₂ W p₂).symm

/-- Remark 1.10.10 (representability, left version): `Hom(X', W) ≃ Hom(𝟙, W ⊗ X)` for an
exact pairing `(X', X)`. -/
noncomputable def remark_1_10_10_representability_left (X X' W : C) [ExactPairing X' X] :
    (X' ⟶ W) ≃ (𝟙_ C ⟶ W ⊗ X) :=
  (Equiv.mk (fun f => (λ_ X').hom ≫ f) (fun g => (λ_ X').inv ≫ g)
    (fun f => by simp) (fun g => by simp)).trans (tensorRightHomEquiv (𝟙_ C) X' X W)

/-- Remark 1.10.10 (left version): Two left duals `X₁`, `X₂` of `Y` have the same hom-out
functor: `Hom(X₁, W) ≃ Hom(X₂, W)`. -/
noncomputable def remark_1_10_10_hom_equiv_left {X₁ X₂ Y : C}
    (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) (W : C) :
    (X₁ ⟶ W) ≃ (X₂ ⟶ W) :=
  (@remark_1_10_10_representability_left C _ _ Y X₁ W p₁).trans
    (@remark_1_10_10_representability_left C _ _ Y X₂ W p₂).symm

end Remark_1_10_10


section TensorExactness_1_10

variable [RigidCategory C]

/-- In a rigid monoidal category, the functor `X ⊗ -` preserves all limits, as it is the
right adjoint of `Xᘁ ⊗ -`. -/
noncomputable instance tensorLeft_preservesLimitsOfSize' (X : C) :
    PreservesLimitsOfSize.{v, v} (tensorLeft X) :=
  (tensorLeftAdjunction X (Xᘁ)).rightAdjoint_preservesLimits

/-- In a rigid monoidal category, the functor `X ⊗ -` preserves all colimits, as it is the
left adjoint of `ᘁX ⊗ -`. -/
noncomputable instance tensorLeft_preservesColimitsOfSize' (X : C) :
    PreservesColimitsOfSize.{v, v} (tensorLeft X) :=
  (tensorLeftAdjunction (ᘁX) X).leftAdjoint_preservesColimits

/-- In a rigid monoidal category, the functor `- ⊗ X` preserves all limits. -/
noncomputable instance tensorRight_preservesLimitsOfSize' (X : C) :
    PreservesLimitsOfSize.{v, v} (tensorRight X) :=
  (tensorRightAdjunction (ᘁX) X).rightAdjoint_preservesLimits

/-- In a rigid monoidal category, the functor `- ⊗ X` preserves all colimits. -/
noncomputable instance tensorRight_preservesColimitsOfSize' (X : C) :
    PreservesColimitsOfSize.{v, v} (tensorRight X) :=
  (tensorRightAdjunction X (Xᘁ)).leftAdjoint_preservesColimits

/-- Specialization of preservation of all limits: `X ⊗ -` preserves finite limits. -/
noncomputable instance tensorLeft_preservesFiniteLimits' (X : C) :
    PreservesFiniteLimits (tensorLeft X) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- Specialization of preservation of all colimits: `X ⊗ -` preserves finite colimits. -/
noncomputable instance tensorLeft_preservesFiniteColimits' (X : C) :
    PreservesFiniteColimits (tensorLeft X) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Specialization of preservation of all limits: `- ⊗ X` preserves finite limits. -/
noncomputable instance tensorRight_preservesFiniteLimits' (X : C) :
    PreservesFiniteLimits (tensorRight X) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- Specialization of preservation of all colimits: `- ⊗ X` preserves finite colimits. -/
noncomputable instance tensorRight_preservesFiniteColimits' (X : C) :
    PreservesFiniteColimits (tensorRight X) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

end TensorExactness_1_10


section Def_1_10_11

/-- Definition 1.10.11 (alias): a rigid monoidal category. -/
abbrev def_1_10_11 := @RigidCategory

/-- Definition 1.10.11: A monoidal category `C` is rigid if every object has both a right
dual and a left dual. -/
abbrev Definition_1_10_11_RigidCategory (C : Type*) [Category C] [MonoidalCategory C] :=
  RigidCategory C

example [RigidCategory C] (X : C) : HasRightDual X := inferInstance

example [RigidCategory C] (X : C) : HasLeftDual X := inferInstance

end Def_1_10_11


section DualityFunctor

/-- The right-duality functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` on a right-rigid category, sending each object
to its right dual. -/
def dualityFunctor_right (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RightRigidCategory C] : C ⥤ (Cᵒᵖ)ᴹᵒᵖ :=
  rightDualFunctor C

/-- The left-duality functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` on a left-rigid category, sending each object
to its left dual. -/
def dualityFunctor_left (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [LeftRigidCategory C] : C ⥤ (Cᵒᵖ)ᴹᵒᵖ :=
  leftDualFunctor C

end DualityFunctor

end TensorCategories
