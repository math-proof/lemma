import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.InternalHom
import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part4
open Category MonoidalCategory LeftModCat


namespace CategoryTheory

/--
[moduleIHomMapRight_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomFunctor.lean)
-/
@[path]
lemma moduleIHomMapRight_id
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [LeftModuleCategory C M]
  [HasModuleInternalHom C M]
  {m₁ m₂ : M} :
-- imply
  moduleIHomMapRight (C := C) m₁ (𝟙 m₂) = 𝟙 (moduleIHom m₁ m₂) := by
-- proof
  simp only [moduleIHomMapRight, comp_id]
  exact (moduleIHomEquiv (moduleIHom m₁ m₂) m₁ m₂).apply_symm_apply (𝟙 _)

end CategoryTheory

namespace CategoryTheory

/--
[moduleIHomMapLeft_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomFunctor.lean)
-/
@[path]
lemma moduleIHomMapLeft_id
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [LeftModuleCategory C M]
  [HasModuleInternalHom C M]
  {m₁ m₂ : M} :
-- imply
  moduleIHomMapLeft (C := C) (𝟙 m₁) m₂ = 𝟙 (moduleIHom m₁ m₂) := by
-- proof
  unfold moduleIHomMapLeft
  rw [LeftModuleCategory.actWhiskerLeft_id, id_comp]
  exact (moduleIHomEquiv (moduleIHom m₁ m₂) m₁ m₂).apply_symm_apply (𝟙 _)
/-- Contravariant functoriality of the internal Hom in the left argument under
composition: `moduleIHomMapLeft (f ≫ g) m₂ = moduleIHomMapLeft g m₂ ≫ moduleIHomMapLeft f m₂`. -/
variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
variable (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
variable [HasModuleInternalHom C M]
/-- Corollary 2.10.5 (part 1): for a fixed object `m₁` of the module category `M`, the
assignment `m₂ ↦ Hom(m₁, m₂)` is a module functor `M ⥤ C`. -/

end CategoryTheory


-- created on 2026-10-23
