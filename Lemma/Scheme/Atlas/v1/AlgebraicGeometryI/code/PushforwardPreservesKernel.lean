import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.PushforwardPreservesKernel
open CategoryTheory CategoryTheory.Limits PresheafOfModules


namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
/--
[pushforward_kernel_iso_inv_ι](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PushforwardPreservesKernel.lean)
-/
@[path]
lemma pushforward_kernel_iso_inv_ι
  {M N : PresheafOfModules.{v} R} (α : M ⟶ N) :
  (pushforward_kernel_iso φ α).inv ≫ (pushforward.{v} φ).map (kernel.ι α) =
    kernel.ι ((pushforward.{v} φ).map α) :=
  PreservesKernel.iso_inv_ι (pushforward φ) α

end PresheafOfModules

/--
[pushforward_kernel_iso_inv_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PushforwardPreservesKernel.lean)
-/
@[path]
private lemma pushforward_kernel_iso_inv__eq
  {C : Type u₁}
  [Category.{v₁} C]
  {D : Type u₂}
  [Category.{v₂} D]
  {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{u}}
  {S : Cᵒᵖ ⥤ RingCat.{u}}
  {φ : S ⟶ F.op ⋙ R}
  {M N : PresheafOfModules.{v} R}
  {α : M ⟶ N} :
-- imply
  (pushforward_kernel_iso φ α).inv ≫ (pushforward.{v} φ).map (kernel.ι α) = kernel.ι ((pushforward.{v} φ).map α) := by
-- proof
  apply PresheafOfModules.pushforward_kernel_iso_inv_ φ α


-- created on 2026-10-23
