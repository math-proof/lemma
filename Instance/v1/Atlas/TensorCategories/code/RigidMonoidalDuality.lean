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
import Def.v1.Atlas.TensorCategories.code.RigidMonoidalDuality
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits MonoidalOpposite Opposite

universe v u


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]


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
end TensorCategories
