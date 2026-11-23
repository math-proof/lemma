module

public import Mathlib
public import Instance.PresheafOfModules_PullbackMonoidal
public import Abbrev.PresheafOfModules_PullbackMonoidal
public import Notation.PresheafOfModules_PullbackMonoidal

public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


universe v u v₁ u₁ v₂ u₂

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal

namespace PresheafOfModules

section restrictScalars

variable {C : Type u₁} [Category.{v₁} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R)

example (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (U : Cᵒᵖ) :
    ((restrictScalars (ringCatHom φ)).obj M).obj U = (restrictScalarsAt φ U).obj (M.obj U) := rfl


public theorem isIso_app_of_isColimit {𝒜 : Type*} [Category 𝒜] {ℬ : Type*} [Category ℬ]
    {J : Type*} [Category J] {H₁ H₂ : 𝒜 ⥤ ℬ} (τ : H₁ ⟶ H₂) {K : J ⥤ 𝒜} {c : Cocone K}
    (hc : IsColimit c) [PreservesColimit K H₁] [PreservesColimit K H₂]
    (h : ∀ j, IsIso (τ.app (K.obj j))) : IsIso (τ.app c.pt) := by
  let hc₁ := isColimitOfPreserves H₁ hc
  let hc₂ := isColimitOfPreserves H₂ hc
  let s : Cocone (K ⋙ H₂) :=
    { pt := H₁.obj c.pt
      ι := { app := fun j => inv (τ.app (K.obj j)) ≫ H₁.map (c.ι.app j)
             naturality := fun j j' g => by
               dsimp
               rw [← cancel_epi (τ.app (K.obj j))]
               simp only [Category.comp_id, IsIso.hom_inv_id_assoc]
               rw [← τ.naturality_assoc, IsIso.hom_inv_id_assoc, ← H₁.map_comp, Cocone.w] } }
  refine ⟨hc₂.desc s, ?_, ?_⟩
  · apply hc₁.hom_ext
    intro j
    have := hc₂.fac s j
    dsimp [s] at this ⊢
    rw [Category.comp_id, τ.naturality_assoc, this, IsIso.hom_inv_id_assoc]
  · apply hc₂.hom_ext
    intro j
    have := hc₂.fac s j
    dsimp [s] at this ⊢
    rw [Category.comp_id, reassoc_of% this, τ.naturality, IsIso.inv_hom_id_assoc]

end CategoryTheory.Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

open scoped PresheafOfModules_PullbackMonoidal


public theorem freeObj_map_freeMk (T : Cᵒᵖ ⥤ Type u) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : T.obj X) :
    (freeObj (R := R') T).map f (ModuleCat.freeMk x) = ModuleCat.freeMk (T.map f x) := by
  simp [freeObj, ModuleCat.freeDesc_apply]


@[simp] public theorem freeμIso_hom_app (F G : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) :
    (freeμIso (R := R) F G).hom.app X =
      (ModuleCat.FreeMonoidal.μIso (R.obj X) (F.obj X) (G.obj X)).hom := rfl

@[simp] public theorem freeεIso_hom_app (X : Cᵒᵖ) :
    (freeεIso (R := R)).hom.app X = (ModuleCat.FreeMonoidal.εIso (R.obj X)).hom := rfl

end PresheafOfModules

namespace PresheafOfModules

namespace PullbackMonoidal

open Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [HasFiniteProducts C] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteProducts F]
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

open scoped PresheafOfModules_PullbackMonoidal


public theorem freeYonedaEquiv_apply' {M : PresheafOfModules.{u} S'} {X : C}
    (f : gS X ⟶ M) : freeYonedaEquiv f = f.app (op X) (ModuleCat.freeMk (𝟙 X)) := rfl

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in

public theorem gS_map_freeMk {U W W' : C} (a : W ⟶ U) (b : W' ⟶ W) :
    (gS (S := S) U).map b.op (ModuleCat.freeMk a) = ModuleCat.freeMk (b ≫ a) := by
  erw [freeObj_map_freeMk]; simp

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in

public theorem gR_map_freeMk {U W W' : D} (a : W ⟶ U) (b : W' ⟶ W) :
    (gR (R := R) U).map b.op (ModuleCat.freeMk a) = ModuleCat.freeMk (b ≫ a) := by
  erw [freeObj_map_freeMk]; simp

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in


public theorem free_map_app_freeMk {E : Type u} [SmallCategory E] {T : Eᵒᵖ ⥤ CommRingCat.{u}}
    {P Q : Eᵒᵖ ⥤ Type u} (ψ : P ⟶ Q) (X : Eᵒᵖ) (x : P.obj X) :
    ((free (T ⋙ forget₂ CommRingCat RingCat)).map ψ).app X (ModuleCat.freeMk x) =
      (ModuleCat.freeMk (ψ.app X x) : ((free (T ⋙ forget₂ CommRingCat RingCat)).obj Q).obj X) := by
  simp
  exact ModuleCat.free_map_apply _ _

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in


public theorem freeμIso_inv_app_freeMk {E : Type u} [SmallCategory E] {T : Eᵒᵖ ⥤ CommRingCat.{u}}
    (P Q : Eᵒᵖ ⥤ Type u) (X : Eᵒᵖ) (z : (P ⊗ Q).obj X) :
    (freeμIso (R := T) P Q).inv.app X (ModuleCat.freeMk z) =
      (ModuleCat.freeMk z.1 ⊗ₜ[T.obj X] ModuleCat.freeMk z.2 :
        (((free (T ⋙ forget₂ CommRingCat RingCat)).obj P).obj X ⊗
          ((free (T ⋙ forget₂ CommRingCat RingCat)).obj Q).obj X :)) :=
  ModuleCat.FreeMonoidal.μIso_inv_freeMk _ z

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in


public theorem tensorHom_app_tmul {E : Type u} [SmallCategory E] {T : Eᵒᵖ ⥤ CommRingCat.{u}}
    {M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)}
    (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Eᵒᵖ) (m : M₁.obj X) (n : M₃.obj X) :
    DFunLike.coe (α := (M₁.obj X ⊗ M₃.obj X :)) (β := fun _ => (M₂.obj X ⊗ M₄.obj X :))
      ((f ⊗ₘ g).app X).hom (m ⊗ₜ[T.obj X] n) = f.app X m ⊗ₜ[T.obj X] g.app X n := by
  erw [PresheafOfModules.tensorHom_app]
  exact ModuleCat.MonoidalCategory.tensorHom_tmul _ _ _ _

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in


public theorem u₂_app_freeMk (U : C) {W : C} (a : W ⟶ U) :
    (u₂ F φ U).app (op W) (ModuleCat.freeMk a) =
      (ModuleCat.freeMk (F.map a) : (gR (R := R) (F.obj U)).obj (op (F.obj W))) := by
  have h1 : (u₂ F φ U).app (op U) (ModuleCat.freeMk (𝟙 U)) =
      (ModuleCat.freeMk (𝟙 (F.obj U)) : (gR (R := R) (F.obj U)).obj (op (F.obj U))) := by
    erw [freeYonedaEquiv_symm_app]; rfl
  have h2 := naturality_apply (u₂ F φ U) a.op (ModuleCat.freeMk (𝟙 U))
  rw [gS_map_freeMk, Category.comp_id] at h2
  rw [h2, h1]
  erw [pushforward_obj_map_apply]
  change (gR (R := R) (F.obj U)).map (F.map a).op (ModuleCat.freeMk (𝟙 (F.obj U))) = _
  rw [gR_map_freeMk, Category.comp_id]


public theorem unit_comp_map_e_hom (U : C) :
    (adj F φ).unit.app (gS U) ≫ (pf F φ).map (e F φ U).hom = u₂ F φ U := by
  change (adj F φ).unit.app (gS U) ≫ (pf F φ).map (((adj F φ).homEquiv _ _).symm (u₂ F φ U)) = _
  erw [← (adj F φ).homEquiv_unit, Equiv.apply_symm_apply]


public theorem yonedaTensorIso_inv_app_apply {E : Type u} [SmallCategory E] [HasFiniteProducts E] (U V : E)
    {W : E} (c : W ⟶ U ⨯ V) :
    (yonedaTensorIso U V).inv.app (op W) c = (c ≫ prod.fst, c ≫ prod.snd) := rfl


public theorem pf_μ_app_tmul (M N : PresheafOfModules.{u} R') (W : C)
    (m : M.obj (op (F.obj W))) (n : N.obj (op (F.obj W))) :
    DFunLike.coe (α := (((pf F φ).obj M).obj (op W) ⊗ ((pf F φ).obj N).obj (op W) :))
      (β := fun _ => ((pf F φ).obj (M ⊗ N)).obj (op W))
      ((μ (pf F φ) M N).app (op W)).hom (m ⊗ₜ[S.obj (op W)] n) = m ⊗ₜ[R.obj (op (F.obj W))] n := by
  change DFunLike.coe (α := (((pf F φ).obj M).obj (op W) ⊗ ((pf F φ).obj N).obj (op W) :))
      (β := fun _ => ((pf F φ).obj (M ⊗ N)).obj (op W))
    ((μ (restrictScalars (ringCatHom (R := F.op ⋙ R) φ))
        ((pushforward₀OfCommRingCat F R).obj M) ((pushforward₀OfCommRingCat F R).obj N) ≫
      (restrictScalars (ringCatHom (R := F.op ⋙ R) φ)).map
        (μ (pushforward₀OfCommRingCat F R) M N)).app (op W)).hom (m ⊗ₜ[S.obj (op W)] n) = _
  rw [show μ (pushforward₀OfCommRingCat F R) M N = 𝟙 _ from rfl, CategoryTheory.Functor.map_id,
    Category.comp_id]
  exact ModuleCat.restrictScalars_μ_tmul _ _ _ m n


public theorem keyL (U V : C) :
    ((j (S := S) U V).inv ≫ ((u₂ F φ U ⊗ₘ u₂ F φ V) ≫
      μ (pf F φ) (gR (F.obj U)) (gR (F.obj V)))).app (op (U ⨯ V)) (ModuleCat.freeMk (𝟙 (U ⨯ V))) =
    (ModuleCat.freeMk (F.map prod.fst) ⊗ₜ[R.obj (op (F.obj (U ⨯ V)))]
      ModuleCat.freeMk (F.map prod.snd) :
      ((gR (R := R) (F.obj U)).obj (op (F.obj (U ⨯ V))) ⊗
        (gR (R := R) (F.obj V)).obj (op (F.obj (U ⨯ V))) :)) := by
  change (μ (pf F φ) (gR (F.obj U)) (gR (F.obj V))).app (op (U ⨯ V))
    (((u₂ F φ U ⊗ₘ u₂ F φ V).app (op (U ⨯ V)))
      ((freeμIso (yoneda.obj U) (yoneda.obj V)).inv.app (op (U ⨯ V))
        (((free S').map (yonedaTensorIso U V).inv).app (op (U ⨯ V))
          (ModuleCat.freeMk (𝟙 (U ⨯ V)))))) = _
  erw [free_map_app_freeMk, yonedaTensorIso_inv_app_apply, freeμIso_inv_app_freeMk]
  erw [tensorHom_app_tmul]
  erw [u₂_app_freeMk, u₂_app_freeMk]
  erw [pf_μ_app_tmul]
  simp only [Category.id_comp]


public theorem keyR (U V : C) :
    (u₂ F φ (U ⨯ V) ≫ (pf F φ).map (r (R := R) F U V).hom).app (op (U ⨯ V))
      (ModuleCat.freeMk (𝟙 (U ⨯ V))) =
    (ModuleCat.freeMk (F.map prod.fst) ⊗ₜ[R.obj (op (F.obj (U ⨯ V)))]
      ModuleCat.freeMk (F.map prod.snd) :
      ((gR (R := R) (F.obj U)).obj (op (F.obj (U ⨯ V))) ⊗
        (gR (R := R) (F.obj V)).obj (op (F.obj (U ⨯ V))) :)) := by
  change ((pf F φ).map (r (R := R) F U V).hom).app (op (U ⨯ V))
    ((u₂ F φ (U ⨯ V)).app (op (U ⨯ V)) (ModuleCat.freeMk (𝟙 (U ⨯ V)))) = _
  erw [u₂_app_freeMk]
  erw [pushforward_map_app_apply]
  change (freeμIso (yoneda.obj (F.obj U)) (yoneda.obj (F.obj V))).inv.app (op (F.obj (U ⨯ V)))
    (((free R').map (yonedaTensorIso (F.obj U) (F.obj V)).inv).app (op (F.obj (U ⨯ V)))
      (((free R').map (yoneda.map (PreservesLimitPair.iso F U V).hom)).app (op (F.obj (U ⨯ V)))
        (ModuleCat.freeMk (F.map (𝟙 (U ⨯ V)))))) = _
  erw [free_map_app_freeMk, free_map_app_freeMk, yonedaTensorIso_inv_app_apply,
    freeμIso_inv_app_freeMk]
  change ModuleCat.freeMk ((F.map (𝟙 (U ⨯ V)) ≫ (PreservesLimitPair.iso F U V).hom) ≫ prod.fst)
      ⊗ₜ[R.obj (op (F.obj (U ⨯ V)))]
    ModuleCat.freeMk ((F.map (𝟙 (U ⨯ V)) ≫ (PreservesLimitPair.iso F U V).hom) ≫ prod.snd) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    PreservesLimitPair.iso_hom, prodComparison_fst, prodComparison_snd]


public theorem key_δ (U V : C) :
    (j (S := S) U V).inv ≫ ((u₂ F φ U ⊗ₘ u₂ F φ V) ≫
      μ (pf F φ) (gR (F.obj U)) (gR (F.obj V))) =
      u₂ F φ (U ⨯ V) ≫ (pf F φ).map (r (R := R) F U V).hom := by
  apply freeYonedaEquiv.injective
  rw [freeYonedaEquiv_apply', freeYonedaEquiv_apply', keyL, keyR]


public theorem δ_gS_comp (U V : C) :
    δ (pb F φ) (gS U) (gS V) ≫ ((e F φ U).hom ⊗ₘ (e F φ V).hom) =
      (pb F φ).map (j (S := S) U V).hom ≫ (e F φ (U ⨯ V)).hom ≫ (r (R := R) F U V).hom := by
  apply ((adj F φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  erw [Adjunction.leftAdjointOplaxMonoidal_δ, Equiv.apply_symm_apply]
  rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural, tensorHom_comp_tensorHom_assoc,
    unit_comp_map_e_hom, unit_comp_map_e_hom,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit, unit_comp_map_e_hom,
    ← cancel_epi (j (S := S) U V).inv, Iso.inv_hom_id_assoc]
  exact key_δ F φ U V

omit [HasFiniteProducts C] [HasFiniteProducts D] [PreservesFiniteProducts F] in


public theorem isIso_app_of_freeYoneda {ℬ : Type*} [Category ℬ]
    {H₁ H₂ : PresheafOfModules.{u} S' ⥤ ℬ}
    [PreservesColimitsOfSize.{u, u} H₁] [PreservesColimitsOfSize.{u, u} H₂] (τ : H₁ ⟶ H₂)
    (h : ∀ U : C, IsIso (τ.app (gS U))) (M : PresheafOfModules.{u} S') : IsIso (τ.app M) := by
  have hcop : ∀ (N : PresheafOfModules.{u} S'), IsIso (τ.app N.freeYonedaCoproduct) := fun N =>
    isIso_app_of_isColimit τ (coproductIsCoproduct (Elements.freeYoneda (M := N)))
      (fun m => h m.as.1.unop)
  have : PreservesColimitsOfSize.{0, 0} H₁ := preservesSmallestColimits_of_preservesColimits H₁
  have : PreservesColimitsOfSize.{0, 0} H₂ := preservesSmallestColimits_of_preservesColimits H₂
  exact isIso_app_of_isColimit τ M.isColimitFreeYonedaCoproductsCokernelCofork
    (by rintro (_ | _) <;> exact hcop _)

omit [HasFiniteProducts D] [PreservesFiniteProducts F] in

public theorem keyL₀ : ((j₀ (S := S)).inv ≫ ε (pf F φ)).app (op (⊤_ C))
      (ModuleCat.freeMk (𝟙 (⊤_ C))) = (1 : R.obj (op (F.obj (⊤_ C)))) := by
  change (ε (pf F φ)).app (op (⊤_ C)) ((freeεIso (R := S)).inv.app (op (⊤_ C))
    (((free S').map (tensorUnitIso C).inv).app (op (⊤_ C)) (ModuleCat.freeMk (𝟙 (⊤_ C))))) = _
  erw [free_map_app_freeMk]
  erw [ModuleCat.FreeMonoidal.εIso_inv_freeMk]

  change (ε (restrictScalars (ringCatHom (R := F.op ⋙ R) φ)) ≫
      (restrictScalars (ringCatHom (R := F.op ⋙ R) φ)).map
        (ε (pushforward₀OfCommRingCat F R))).app (op (⊤_ C)) (1 : S.obj (op (⊤_ C))) = _
  rw [show ε (pushforward₀OfCommRingCat F R) = 𝟙 _ from rfl, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [ModuleCat.restrictScalars_η]
  exact (φ.app (op (⊤_ C))).hom.map_one


public theorem keyR₀ : (u₂ F φ (⊤_ C) ≫ (pf F φ).map (r₀ (R := R) F).hom).app (op (⊤_ C))
      (ModuleCat.freeMk (𝟙 (⊤_ C))) = (1 : R.obj (op (F.obj (⊤_ C)))) := by
  change ((pf F φ).map (r₀ (R := R) F).hom).app (op (⊤_ C))
    ((u₂ F φ (⊤_ C)).app (op (⊤_ C)) (ModuleCat.freeMk (𝟙 (⊤_ C)))) = _
  erw [u₂_app_freeMk]
  erw [pushforward_map_app_apply]
  change (freeεIso (R := R)).inv.app (op (F.obj (⊤_ C)))
    (((free R').map (tensorUnitIso D).inv).app (op (F.obj (⊤_ C)))
      (((free R').map (yoneda.map (PreservesTerminal.iso F).hom)).app (op (F.obj (⊤_ C)))
        (ModuleCat.freeMk (F.map (𝟙 (⊤_ C)))))) = _
  erw [free_map_app_freeMk, free_map_app_freeMk]
  exact ModuleCat.FreeMonoidal.εIso_inv_freeMk _ _


public theorem key_η : (j₀ (S := S)).inv ≫ ε (pf F φ) = u₂ F φ (⊤_ C) ≫ (pf F φ).map (r₀ (R := R) F).hom := by
  apply freeYonedaEquiv.injective
  rw [freeYonedaEquiv_apply', freeYonedaEquiv_apply', keyL₀, keyR₀]


public theorem η_eq : η (pb F φ) = (pb F φ).map (j₀ (S := S)).hom ≫ (e F φ (⊤_ C)).hom ≫ (r₀ (R := R) F).hom := by
  apply ((adj F φ).homEquiv _ _).injective
  erw [Adjunction.leftAdjointOplaxMonoidal_η, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit, unit_comp_map_e_hom,
    ← cancel_epi (j₀ (S := S)).inv, Iso.inv_hom_id_assoc]
  exact key_η F φ

end PullbackMonoidal

end PresheafOfModules


-- created on 2026-10-24
-- updated on 2026-11-14
