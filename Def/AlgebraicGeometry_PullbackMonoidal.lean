module
public import Mathlib
public import Instance.PresheafOfModules_PullbackMonoidal
public import Abbrev.PresheafOfModules_PullbackMonoidal
public import Notation.PresheafOfModules_PullbackMonoidal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


public section

universe v u v₁ u₁ v₂ u₂

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal

namespace PresheafOfModules

section restrictScalars

variable {C : Type u₁} [Category.{v₁} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R)

noncomputable def restrictScalarsε :
    𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ _ _)) ⟶
      (restrictScalars (ringCatHom φ)).obj (𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ _ _))) where
  app U := ε (restrictScalarsAt φ U)
  naturality {U V} i := by
    refine ModuleCat.hom_ext (LinearMap.ext fun (s : S.obj U) => ?_)
    change ε (restrictScalarsAt φ V) (S.map i s) = R.map i (ε (restrictScalarsAt φ U) s)
    erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
    exact ConcreteCategory.congr_hom (φ.naturality i) s

noncomputable def restrictScalarsμ (M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (restrictScalars (ringCatHom φ)).obj M ⊗ (restrictScalars (ringCatHom φ)).obj N ⟶
      (restrictScalars (ringCatHom φ)).obj (M ⊗ N) where
  app U := μ (restrictScalarsAt φ U) (M.obj U) (N.obj U)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    dsimp
    erw [Monoidal.tensorObj_map_tmul]
    erw [ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul]
    erw [Monoidal.tensorObj_map_tmul]
    rfl

end restrictScalars

section pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

end pushforward

end PresheafOfModules


namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

open scoped PresheafOfModules_PullbackMonoidal

noncomputable def freeεIso :
    𝟙_ (PresheafOfModules.{u} R') ≅ (free R').obj (𝟙_ (Cᵒᵖ ⥤ Type u)) :=
  isoMk (fun X => ModuleCat.FreeMonoidal.εIso (R.obj X)) (by
    intro X Y f
    refine ModuleCat.hom_ext (LinearMap.ext fun (r : R.obj X) => ?_)
    have h1 : ∀ (Z : Cᵒᵖ) (s : R.obj Z), (ModuleCat.FreeMonoidal.εIso (R.obj Z)).hom s =
        s • ModuleCat.freeMk PUnit.unit := fun Z s => by
      have := (ModuleCat.FreeMonoidal.εIso (R.obj Z)).hom.hom.map_smul s (1 : R.obj Z)
      rw [smul_eq_mul, mul_one] at this
      exact this
    change (ModuleCat.FreeMonoidal.εIso (R.obj Y)).hom ((unit R').map f r) =
      ((free R').obj (𝟙_ (Cᵒᵖ ⥤ Type u))).map f
        ((ModuleCat.FreeMonoidal.εIso (R.obj X)).hom r)
    rw [h1, h1, PresheafOfModules.map_smul]
    erw [freeObj_map_freeMk]
    rfl)

noncomputable def freeμIso (F G : Cᵒᵖ ⥤ Type u) :
    (free R').obj F ⊗ (free R').obj G ≅ (free R').obj (F ⊗ G) :=
  isoMk (fun X => ModuleCat.FreeMonoidal.μIso (R.obj X) (F.obj X) (G.obj X)) (by
    intro X Y f
    rw [← cancel_epi (ModuleCat.FreeMonoidal.μIso (R.obj X) (F.obj X) (G.obj X)).inv,
      Iso.inv_hom_id_assoc]
    apply ModuleCat.free_hom_ext
    rintro ⟨x, y⟩
    change (ModuleCat.FreeMonoidal.μIso (R.obj Y) (F.obj Y) (G.obj Y)).hom
      (((free R').obj F ⊗ (free R').obj G).map f
        ((ModuleCat.FreeMonoidal.μIso (R.obj X) (F.obj X) (G.obj X)).inv (ModuleCat.freeMk (x, y)))) =
      ((free R').obj (F ⊗ G)).map f (ModuleCat.freeMk (x, y))
    erw [ModuleCat.FreeMonoidal.μIso_inv_freeMk]
    erw [Monoidal.tensorObj_map_tmul]
    erw [freeObj_map_freeMk, freeObj_map_freeMk, freeObj_map_freeMk]
    erw [ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk]
    rfl)

end PresheafOfModules

namespace PresheafOfModules

namespace PullbackMonoidal

open Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [HasFiniteProducts C] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteProducts F]
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

open scoped PresheafOfModules_PullbackMonoidal

noncomputable def u₂ (U : C) : gS U ⟶ (pf F φ).obj (gR (F.obj U)) :=
  (h₂ F φ U).homEquiv (𝟙 _)

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in
noncomputable def e (U : C) : (pb F φ).obj (gS U) ≅ gR (F.obj U) where
  hom := ((adj F φ).homEquiv _ _).symm (u₂ F φ U)
  inv := (h₂ F φ U).homEquiv.symm ((adj F φ).unit.app (gS U))
  hom_inv_id := ((adj F φ).homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    have := (h₂ F φ U).homEquiv_comp ((h₂ F φ U).homEquiv.symm ((adj F φ).unit.app (gS U))) (𝟙 _)
    rw [Category.id_comp, Equiv.apply_symm_apply] at this

    erw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id, Category.comp_id]
    exact this.symm)
  inv_hom_id := (h₂ F φ U).homEquiv.injective (by
    rw [(h₂ F φ U).homEquiv_comp, Equiv.apply_symm_apply]
    change (adj F φ).unit.app (gS U) ≫ (pf F φ).map (((adj F φ).homEquiv _ _).symm (u₂ F φ U)) =
      (h₂ F φ U).homEquiv (𝟙 _)
    erw [← (adj F φ).homEquiv_unit, Equiv.apply_symm_apply]
    rfl)

noncomputable def yonedaTensorIso {E : Type u} [SmallCategory E] [HasFiniteProducts E] (U V : E) :
    yoneda.obj U ⊗ yoneda.obj V ≅ yoneda.obj (U ⨯ V) :=
  NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun p => prod.lift p.1 p.2
      invFun := fun c => (c ≫ prod.fst, c ≫ prod.snd)
      left_inv := fun p => Prod.ext (prod.lift_fst _ _) (prod.lift_snd _ _)
      right_inv := fun c => by apply Limits.prod.hom_ext <;> simp }) (by
    intro W W' f
    ext p
    change prod.lift ((yoneda.obj U ⊗ yoneda.obj V).map f p).1
        ((yoneda.obj U ⊗ yoneda.obj V).map f p).2 = f.unop ≫ prod.lift p.1 p.2
    erw [Monoidal.tensorObj_map, tensor_apply]
    apply Limits.prod.hom_ext <;> simp)

noncomputable def tensorUnitIso (E : Type u) [SmallCategory E] [HasFiniteProducts E] :
    𝟙_ (Eᵒᵖ ⥤ Type u) ≅ yoneda.obj (⊤_ E) :=
  NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun _ => terminal.from _
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun c => (terminal.hom_ext _ _) }) (by
    intro W W' f; ext p; apply terminal.hom_ext)

noncomputable def j (U V : C) : gS (S := S) U ⊗ gS V ≅ gS (U ⨯ V) :=
  freeμIso (yoneda.obj U) (yoneda.obj V) ≪≫ (free S').mapIso (yonedaTensorIso U V)

noncomputable def j₀ : 𝟙_ (PresheafOfModules.{u} S') ≅ gS (S := S) (⊤_ C) :=
  freeεIso ≪≫ (free S').mapIso (tensorUnitIso C)

noncomputable def r (U V : C) : gR (R := R) (F.obj (U ⨯ V)) ≅ gR (F.obj U) ⊗ gR (F.obj V) :=
  (free R').mapIso (yoneda.mapIso (PreservesLimitPair.iso F U V)) ≪≫
    ((free R').mapIso (yonedaTensorIso (F.obj U) (F.obj V))).symm ≪≫
    (freeμIso (yoneda.obj (F.obj U)) (yoneda.obj (F.obj V))).symm

noncomputable def r₀ : gR (R := R) (F.obj (⊤_ C)) ≅ 𝟙_ _ :=
  (free R').mapIso (yoneda.mapIso (PreservesTerminal.iso F)) ≪≫
    ((free R').mapIso (tensorUnitIso D)).symm ≪≫ freeεIso.symm

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in

end PullbackMonoidal

end PresheafOfModules


-- created on 2026-10-24
-- updated on 2026-11-14
