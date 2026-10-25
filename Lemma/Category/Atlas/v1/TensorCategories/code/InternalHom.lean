import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
open CategoryTheory
open Category MonoidalCategory LeftModCat


namespace CategoryTheory

/--
[actWhiskerLeft_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean)
-/
@[path]
lemma actWhiskerLeft_comp
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {X : C}
  {M₁ M₂ M₃ : M}
  {f : M₁ ⟶ M₂}
  {g : M₂ ⟶ M₃} :
-- imply
  X ◁ᵐ (f ≫ g) = X ◁ᵐ f ≫ X ◁ᵐ g := by
-- proof
  have h := LeftModuleCategory.actTensorHom_comp (M := M) (𝟙 X) f (𝟙 X) g
  simp [LeftModuleCategory.actTensorHom_def] at h; exact h.symm

end CategoryTheory

namespace CategoryTheory

/--
[actWhisker_interchange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean)
-/
@[path]
lemma actWhisker_interchange
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {X₁ X₂ : C}
  {M₁ M₂ : M}
  {f : X₁ ⟶ X₂}
  {g : M₁ ⟶ M₂} :
-- imply
  f ▷ᵐ M₁ ≫ X₂ ◁ᵐ g = X₁ ◁ᵐ g ≫ f ▷ᵐ M₂ := by
-- proof
  have h1 := LeftModuleCategory.actTensorHom_def (M := M) f g
  have h2 := LeftModuleCategory.actTensorHom_comp (M := M) (𝟙 X₁) g f (𝟙 M₂)
  rw [id_comp, comp_id] at h2
  rw [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actTensorHom_def] at h2
  simp at h2; rw [← h1, ← h2]

end CategoryTheory

namespace CategoryTheory

/--
[moduleIHomEquiv_natural_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean)
-/
@[path]
lemma moduleIHomEquiv_natural_right
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {X : C}
  {m₁ : M}
  {m₂ m₂' : M}
  {g : m₂ ⟶ m₂'}
-- given
  (h : X ⊗ᵐ m₁ ⟶ m₂) :
-- imply
  moduleIHomEquiv X m₁ m₂' (h ≫ g) = moduleIHomEquiv X m₁ m₂ h ≫ moduleIHomMapRight m₁ g := by
-- proof
  rw [moduleIHomMapRight]
  rw [← moduleIHomEquiv_natural]
  have key := moduleIHomEquiv_symm_eq X m₁ m₂ (moduleIHomEquiv X m₁ m₂ h)
  rw [Equiv.symm_apply_apply] at key
  congr 1
  conv_lhs => rw [key]
  rw [assoc]

end CategoryTheory

namespace CategoryTheory

/--
[moduleIHomRight_preserves_mono_proof](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean)
-/
@[path]
lemma moduleIHomRight_preserves_mono_proof
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {M : Type u₂}
  [Category.{v₂} M]
  [LeftModuleCategory C M]
  [HasModuleInternalHom C M]
  {m₁ : M}
  {m₂ m₂' : M}
  {f : m₂ ⟶ m₂'}
-- given
  (hf : Mono f) :
-- imply
  Mono (moduleIHomMapRight (C := C) m₁ f) := by
-- proof
  constructor
  intro X g h hgh
  apply (moduleIHomEquiv X m₁ m₂).symm.injective
  have hg := moduleIHomEquiv_natural_right X m₁ f ((moduleIHomEquiv X m₁ m₂).symm g)
  rw [Equiv.apply_symm_apply] at hg
  have hh := moduleIHomEquiv_natural_right X m₁ f ((moduleIHomEquiv X m₁ m₂).symm h)
  rw [Equiv.apply_symm_apply] at hh
  have key : (moduleIHomEquiv X m₁ m₂).symm g ≫ f =
    (moduleIHomEquiv X m₁ m₂).symm h ≫ f := by
    apply (moduleIHomEquiv X m₁ m₂').injective
    rw [hg, hh, hgh]
  exact hf.right_cancellation _ _ key
/-- In an exact module category, if `f : m₂ ⟶ m₂'` is an epimorphism, then
`moduleIHomMapRight m₁ f` is also an epimorphism (Corollary 2.10.6, exactness in `m₂`). -/

end CategoryTheory

/--
[moduleIHomEquiv_symm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean)
-/
@[path]
private lemma moduleIHomEquiv_symm_eq_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {X : C}
  {m n : M}
-- given
  (h : X ⟶ moduleIHom (C := C) m n) :
-- imply
  (moduleIHomEquiv X m n).symm h = h ▷ᵐ m ≫ moduleIHomEv m n := by
-- proof
  apply CategoryTheory.moduleIHomEquiv_symm_eq X m n h

/--
[actWhiskerRight_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean)
-/
@[path]
private lemma actWhiskerRight_comp_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {X₁ X₂ X₃ : C}
  {f : X₁ ⟶ X₂}
  {g : X₂ ⟶ X₃}
  {N : M} :
-- imply
  (f ≫ g) ▷ᵐ N = f ▷ᵐ N ≫ g ▷ᵐ N := by
-- proof
  apply CategoryTheory.actWhiskerRight_comp f g N

/--
[moduleIHom_curry_equiv_symm_natural](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean)
-/
@[path]
private lemma moduleIHom_curry_equiv_symm_natural_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {T₁ T₂ X : C}
  {m n : M}
  {f : T₁ ⟶ T₂}
-- given
  (g : T₂ ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n) :
-- imply
  (moduleIHom_curry_equiv T₁ X m n).symm (f ≫ g) = f ▷ X ≫ (moduleIHom_curry_equiv T₂ X m n).symm g := by
-- proof
  apply CategoryTheory.moduleIHom_curry_equiv_symm_natural f g

/--
[moduleIHom_tensor_equiv_natural](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean)
-/
@[path]
private lemma moduleIHom_tensor_equiv_natural_eq
  {C : Type u₁}
  [Category.{v₁} C]
  [MonoidalCategory C]
  {Y₁ Y₂ X : C}
  [HasRightDual X]
  {m n : M}
  {f : Y₁ ⟶ Y₂}
-- given
  (g : Y₂ ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n) :
-- imply
  moduleIHom_tensor_equiv Y₁ X m n (f ≫ g) = f ≫ moduleIHom_tensor_equiv Y₂ X m n g := by
-- proof
  apply CategoryTheory.moduleIHom_tensor_equiv_natural f g


-- created on 2026-10-23
