import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.DualCategory.Part6
open CategoryTheory CategoryTheory.DualCatObj
open Category MonoidalCategory LeftModCat Limits


namespace CategoryTheory.DualCatObj

/--
[Hom.mkInverse_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
lemma Hom.mkInverse_comp
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F : DualCatObj C M}
-- given
  (α : Hom F (idModuleFunctor (C := C) (M := M)))
  (hiso : ∀ (N : M), IsIso (α.natTrans.app N)) :
-- imply
  Hom.comp (Hom.mkInverse α hiso) α = Hom.id (idModuleFunctor (C := C) (M := M)) := by
-- proof
  apply Hom.ext'
  ext N
  simp only [Hom.comp, Hom.mkInverse, Hom.id, NatTrans.comp_app, NatTrans.id_app']
  haveI := hiso N
  exact IsIso.inv_hom_id (α.natTrans.app N)

end CategoryTheory.DualCatObj

namespace CategoryTheory.DualCatObj

/--
[Hom.comp_mkInverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
lemma Hom.comp_mkInverse
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F : DualCatObj C M}
-- given
  (α : Hom F (idModuleFunctor (C := C) (M := M)))
  (hiso : ∀ (N : M), IsIso (α.natTrans.app N)) :
-- imply
  Hom.comp α (Hom.mkInverse α hiso) = Hom.id F := by
-- proof
  apply Hom.ext'
  ext N
  simp only [Hom.comp, Hom.mkInverse, Hom.id, NatTrans.comp_app, NatTrans.id_app']
  haveI := hiso N
  exact IsIso.hom_inv_id (α.natTrans.app N)
set_option maxHeartbeats 800000 in

end CategoryTheory.DualCatObj

/--
[Hom.ext'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma ext'_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F G : DualCatObj C M}
  {f g : Hom F G}
-- given
  (h : f.natTrans = g.natTrans) :
-- imply
  f = g := by
-- proof
  apply CategoryTheory.DualCatObj.Hom.ext' C M h

/--
[id_natTrans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma id_natTrans_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F : DualCatObj C M} :
-- imply
  (𝟙 F : Hom F F).natTrans = NatTrans.id F.toFunctor := by
-- proof
  apply CategoryTheory.DualCatObj.id_natTrans C M F

/--
[comp_natTrans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma comp_natTrans_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F G H : DualCatObj C M}
  {f : F ⟶ G}
  {g : G ⟶ H} :
-- imply
  (f ≫ g).natTrans = f.natTrans ≫ g.natTrans := by
-- proof
  apply CategoryTheory.DualCatObj.comp_natTrans C M f g

/--
[compModuleFunctor_assoc_strIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma compModuleFunctor_assoc_strIso_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F₁ F₂ F₃ : DualCatObj C M}
  {X : C}
  {N : M} :
-- imply
  (compModuleFunctor (compModuleFunctor F₁ F₂) F₃).strIso X N = (compModuleFunctor F₁ (compModuleFunctor F₂ F₃)).strIso X N := by
-- proof
  apply CategoryTheory.DualCatObj.compModuleFunctor_assoc_strIso C M F₁ F₂ F₃ X N

/--
[compModuleFunctor_left_id_strIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma compModuleFunctor_left_id_strIso_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F : DualCatObj C M}
  {X : C}
  {N : M} :
-- imply
  (compModuleFunctor idModuleFunctor F).strIso X N = F.strIso X N := by
-- proof
  apply CategoryTheory.DualCatObj.compModuleFunctor_left_id_strIso C M F X N

/--
[compModuleFunctor_right_id_strIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma compModuleFunctor_right_id_strIso_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F : DualCatObj C M}
  {X : C}
  {N : M} :
-- imply
  (compModuleFunctor F idModuleFunctor).strIso X N = F.strIso X N := by
-- proof
  apply CategoryTheory.DualCatObj.compModuleFunctor_right_id_strIso C M F X N

/--
[tensorObj_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma tensorObj_eq_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F G : DualCatObj C M} :
-- imply
  F ⊗ G = compModuleFunctor F G := by
-- proof
  apply CategoryTheory.DualCatObj.tensorObj_eq C M F G

/--
[tensorUnit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma tensorUnit_eq_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M} :
-- imply
  (𝟙_ (DualCatObj C M)) = idModuleFunctor := by
-- proof
  apply CategoryTheory.DualCatObj.tensorUnit_eq C M

/--
[whiskerLeft_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma whiskerLeft_eq_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F : DualCatObj C M}
  {G₁ G₂ : DualCatObj C M}
  {f : G₁ ⟶ G₂} :
-- imply
  F ◁ f = dualWhiskerLeft F f := by
-- proof
  apply CategoryTheory.DualCatObj.whiskerLeft_eq C M F f

/--
[whiskerRight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma whiskerRight_eq_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F₁ F₂ : DualCatObj C M}
  {f : F₁ ⟶ F₂}
  {G : DualCatObj C M} :
-- imply
  f ▷ G = dualWhiskerRight f G := by
-- proof
  apply CategoryTheory.DualCatObj.whiskerRight_eq C M f G

/--
[associator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma associator_eq_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F₁ F₂ F₃ : DualCatObj C M} :
-- imply
  α_ F₁ F₂ F₃ = dualAssociator F₁ F₂ F₃ := by
-- proof
  apply CategoryTheory.DualCatObj.associator_eq C M F₁ F₂ F₃

/--
[leftUnitor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma leftUnitor_eq_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F : DualCatObj C M} :
-- imply
  λ_ F = dualLeftUnitor F := by
-- proof
  apply CategoryTheory.DualCatObj.leftUnitor_eq C M F

/--
[rightUnitor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma rightUnitor_eq_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {F : DualCatObj C M} :
-- imply
  ρ_ F = dualRightUnitor F := by
-- proof
  apply CategoryTheory.DualCatObj.rightUnitor_eq C M F

/--
[actWhiskerLeft_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma actWhiskerLeft_comp_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  {X : C}
  {A B D : M}
  {f : A ⟶ B}
  {g : B ⟶ D} :
-- imply
  X ◁ᵐ (f ≫ g) = X ◁ᵐ f ≫ X ◁ᵐ g := by
-- proof
  apply CategoryTheory.DualCatObj.actWhiskerLeft_comp C M X f g

/--
[DoubleDualHom.ext'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma ext'_eq_2
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C M}
  [inst : LeftModuleCategory (DualCatObj C M) M]
  {F G : DoubleDualObj C M}
  {f g : DoubleDualHom F G}
-- given
  (h : f.natTrans = g.natTrans) :
-- imply
  f = g := by
-- proof
  apply CategoryTheory.DualCatObj.DoubleDualHom.ext' C M h

/--
[DrinfeldCenterHalfBraidingHom.ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean)
-/
@[path]
private lemma ext_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {M : Type u}
  [Category.{v} M]
  [LeftModuleCategory C M]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {P Q : DrinfeldCenterHalfBraidingObj C}
  {f g : DrinfeldCenterHalfBraidingHom P Q}
-- given
  (h : f.hom = g.hom) :
-- imply
  f = g := by
-- proof
  apply CategoryTheory.DrinfeldCenterHalfBraidingHom.ext C M h


-- created on 2026-10-23
