/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PushforwardPreservesKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Instance.v1.Atlas.AlgebraicGeometryI.code.PushforwardPreservesKernel
open CategoryTheory CategoryTheory.Limits

universe v v₁ v₂ u₁ u₂ u

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]


namespace PresheafOfModules

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- Pushforward preserves kernels: the kernel of the pushforward of `α` is isomorphic
to the pushforward of the kernel of `α`. -/
noncomputable def pushforward_kernel_iso
    {M N : PresheafOfModules.{v} R} (α : M ⟶ N) :
    (pushforward.{v} φ).obj (kernel α) ≅ kernel ((pushforward.{v} φ).map α) :=
  PreservesKernel.iso (pushforward φ) α

end PresheafOfModules
