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
import Theorem.v1.Atlas.TensorCategories.code.TensorExact.Part2
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Opposite

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

section ExactFunctors

/-- The right dualization functor `Cᵒᵖ ⥤ C` is faithful, as the right adjoint mate is injective. -/
instance rightDualizationFunctor_faithful :
    (rightDualizationFunctor (C := C)).Faithful where
  map_injective {X Y f₁ f₂} h := by
    apply Quiver.Hom.unop_inj
    apply (rightAdjointMateEquiv Y.unop X.unop).injective
    simp only [rightAdjointMateEquiv_apply]
    exact h

/-- The right dualization functor `Cᵒᵖ ⥤ C` is full, as the right adjoint mate is surjective. -/
instance rightDualizationFunctor_full :
    (rightDualizationFunctor (C := C)).Full where
  map_surjective {X Y} g := by
    obtain ⟨h, hh⟩ := (rightAdjointMateEquiv Y.unop X.unop).surjective g
    exact ⟨h.op, by simp [rightDualizationFunctor, ← rightAdjointMateEquiv_apply, hh]⟩

/-- The right dualization functor `Cᵒᵖ ⥤ C` is essentially surjective: every `Z` is `(ᘁZ)ᘁ`. -/
instance rightDualizationFunctor_essSurj :
    (rightDualizationFunctor (C := C)).EssSurj where
  mem_essImage Z := by
    refine ⟨op (ᘁZ), ⟨?_⟩⟩
    change rightDualizationFunctor.obj (op (ᘁZ)) ≅ Z
    simp only [rightDualizationFunctor]


    exact rightDualIso (RightRigidCategory.rightDual (ᘁZ)).exact hasRightDualLeftDual.exact

/-- The right dualization functor `Cᵒᵖ ⥤ C` is an equivalence of categories. -/
noncomputable instance rightDualizationFunctor_isEquivalence :
    (rightDualizationFunctor (C := C)).IsEquivalence where

/-- The right dualization functor preserves all limits, since it is an equivalence. -/
noncomputable instance rightDualizationFunctor_preservesLimits :
    PreservesLimitsOfSize.{v, v} (rightDualizationFunctor (C := C)) :=
  inferInstance

/-- The right dualization functor preserves all colimits, since it is an equivalence. -/
noncomputable instance rightDualizationFunctor_preservesColimits :
    PreservesColimitsOfSize.{v, v} (rightDualizationFunctor (C := C)) :=
  inferInstance

/-- The right dualization functor preserves finite limits. -/
noncomputable instance rightDualizationFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (rightDualizationFunctor (C := C)) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The right dualization functor preserves finite colimits. -/
noncomputable instance rightDualizationFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (rightDualizationFunctor (C := C)) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The left dualization functor `Cᵒᵖ ⥤ C` is faithful, as the left adjoint mate is injective. -/
instance leftDualizationFunctor_faithful :
    (leftDualizationFunctor (C := C)).Faithful where
  map_injective {X Y f₁ f₂} h := by
    apply Quiver.Hom.unop_inj
    apply (leftAdjointMateEquiv Y.unop X.unop).injective
    simp only [leftAdjointMateEquiv_apply]
    exact h

/-- The left dualization functor `Cᵒᵖ ⥤ C` is full, as the left adjoint mate is surjective. -/
instance leftDualizationFunctor_full :
    (leftDualizationFunctor (C := C)).Full where
  map_surjective {X Y} g := by
    obtain ⟨h, hh⟩ := (leftAdjointMateEquiv Y.unop X.unop).surjective g
    exact ⟨h.op, by simp [leftDualizationFunctor, ← leftAdjointMateEquiv_apply, hh]⟩

/-- The left dualization functor `Cᵒᵖ ⥤ C` is essentially surjective: every `Z` is `ᘁ(Zᘁ)`. -/
instance leftDualizationFunctor_essSurj :
    (leftDualizationFunctor (C := C)).EssSurj where
  mem_essImage Z := by
    refine ⟨op (Zᘁ), ⟨?_⟩⟩
    change leftDualizationFunctor.obj (op (Zᘁ)) ≅ Z
    simp only [leftDualizationFunctor]


    exact leftDualIso (LeftRigidCategory.leftDual (Zᘁ)).exact hasLeftDualRightDual.exact

/-- The left dualization functor `Cᵒᵖ ⥤ C` is an equivalence of categories. -/
noncomputable instance leftDualizationFunctor_isEquivalence :
    (leftDualizationFunctor (C := C)).IsEquivalence where

/-- The left dualization functor preserves all limits, since it is an equivalence. -/
noncomputable instance leftDualizationFunctor_preservesLimits :
    PreservesLimitsOfSize.{v, v} (leftDualizationFunctor (C := C)) :=
  inferInstance

/-- The left dualization functor preserves all colimits, since it is an equivalence. -/
noncomputable instance leftDualizationFunctor_preservesColimits :
    PreservesColimitsOfSize.{v, v} (leftDualizationFunctor (C := C)) :=
  inferInstance

/-- The left dualization functor preserves finite limits. -/
noncomputable instance leftDualizationFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (leftDualizationFunctor (C := C)) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The left dualization functor preserves finite colimits. -/
noncomputable instance leftDualizationFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (leftDualizationFunctor (C := C)) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

end ExactFunctors
end CategoryTheory
