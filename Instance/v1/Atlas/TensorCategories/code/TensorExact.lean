/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Abelian.Basic
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Opposite

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

section TensorLeftExact

/-- In a rigid category, the left-tensor functor `X ⊗ -` preserves all limits, as it is the
right adjoint of `Xᘁ ⊗ -`. -/
noncomputable instance tensorLeft_preservesLimitsOfSize (X : C) :
    PreservesLimitsOfSize.{v, v} (tensorLeft X) :=
  (tensorLeftAdjunction X (Xᘁ)).rightAdjoint_preservesLimits

/-- In a rigid category, the left-tensor functor `X ⊗ -` preserves all colimits, as it is the
left adjoint of `ᘁX ⊗ -`. -/
noncomputable instance tensorLeft_preservesColimitsOfSize (X : C) :
    PreservesColimitsOfSize.{v, v} (tensorLeft X) :=
  (tensorLeftAdjunction (ᘁX) X).leftAdjoint_preservesColimits

/-- The left-tensor functor `X ⊗ -` in a rigid category preserves finite limits. -/
noncomputable instance tensorLeft_preservesFiniteLimits (X : C) :
    PreservesFiniteLimits (tensorLeft X) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The left-tensor functor `X ⊗ -` in a rigid category preserves finite colimits. -/
noncomputable instance tensorLeft_preservesFiniteColimits (X : C) :
    PreservesFiniteColimits (tensorLeft X) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

end TensorLeftExact

section TensorRightExact

/-- In a rigid category, the right-tensor functor `- ⊗ X` preserves all limits, as it is the
right adjoint of `- ⊗ ᘁX`. -/
noncomputable instance tensorRight_preservesLimitsOfSize (X : C) :
    PreservesLimitsOfSize.{v, v} (tensorRight X) :=
  (tensorRightAdjunction (ᘁX) X).rightAdjoint_preservesLimits

/-- In a rigid category, the right-tensor functor `- ⊗ X` preserves all colimits, as it is the
left adjoint of `- ⊗ Xᘁ`. -/
noncomputable instance tensorRight_preservesColimitsOfSize (X : C) :
    PreservesColimitsOfSize.{v, v} (tensorRight X) :=
  (tensorRightAdjunction X (Xᘁ)).leftAdjoint_preservesColimits

/-- The right-tensor functor `- ⊗ X` in a rigid category preserves finite limits. -/
noncomputable instance tensorRight_preservesFiniteLimits (X : C) :
    PreservesFiniteLimits (tensorRight X) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The right-tensor functor `- ⊗ X` in a rigid category preserves finite colimits. -/
noncomputable instance tensorRight_preservesFiniteColimits (X : C) :
    PreservesFiniteColimits (tensorRight X) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

end TensorRightExact
end CategoryTheory
