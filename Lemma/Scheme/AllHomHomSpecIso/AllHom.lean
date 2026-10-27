import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma appLE_congr_hom
  {X Y : (Scheme : Type 1)}
  {g g' : X ⟶ Y}
  {U : Y.Opens}
  {V : X.Opens}
  -- given
  (hg : g = g')
  (h : V ≤ ((TopologicalSpace.Opens.map g.base).obj U))
  (h' : V ≤ ((TopologicalSpace.Opens.map g'.base).obj U)) :
  -- imply
  g.appLE U V h = g'.appLE U V h' := by
  -- proof
  subst hg
  rfl

/--
[CerednikDrinfeld_eval_app_pullback_fst_eq_algebraMap_eval_app](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_eval_app_pullback_fst_eq_algebraMap_eval_app.lean)
-/
@[path]
private lemma main
  {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
  {𝒳 S : (Scheme : Type 1)}
  {f : 𝒳 ⟶ S}
  {sC : Spec (CommRingCat.of C) ⟶ S}
  {p : Spec (CommRingCat.of R) ⟶ 𝒳}
  {q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC}
  {V : 𝒳.Opens}
  {W : (Limits.pullback f sC).Opens}
  -- given
  (hq₁ : q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p)
  (hq₂ : q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)))
  (hpV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ((TopologicalSpace.Opens.map p.base).obj V))
  (hWV : W ≤ ((TopologicalSpace.Opens.map (Limits.pullback.fst f sC).base).obj V))
  (hqW : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ ((TopologicalSpace.Opens.map q.base).obj W)) :
  -- imply
  (∀ s : 𝒳.presheaf.obj (Opposite.op V), (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqW).op).hom ((q.app W).hom (((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom s)))) = algebraMap R C ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hpV).op).hom ((p.app V).hom s)))) ∧ (∀ c : C, (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqW).op).hom ((q.app W).hom (((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c))))) = c) := by
  -- proof
  constructor
  ·
    intro s
    have hq : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ ((TopologicalSpace.Opens.map (q ≫ Limits.pullback.fst f sC).base).obj V) := by
      rw [Scheme.Hom.comp_preimage]
      apply hqW.trans (Scheme.Hom.preimage_mono q hWV)
    have h1 : ((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqW).op).hom ((q.app W).hom (((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom s))) = ((q ≫ Limits.pullback.fst f sC).appLE V ⊤ hq).hom s := by
      rw [← Scheme.Hom.appLE_comp_appLE q (Limits.pullback.fst f sC) V W ⊤ hWV hqW]
      rfl
    have hq' : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ ((TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p).base).obj V) := by
      rw [Scheme.Hom.comp_preimage]
      apply le_top.trans (Scheme.Hom.preimage_mono _ hpV)
    rw [h1, appLE_congr_hom hq₁ hq hq', ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (algebraMap R C))) p V ⊤ ⊤ hpV le_top]
    have h2 : (Spec.map (CommRingCat.ofHom (algebraMap R C))).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom (algebraMap R C))).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [h2]
    change ((p.appLE V ⊤ hpV ≫ (Spec.map (CommRingCat.ofHom (algebraMap R C))).appTop) ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom s = algebraMap R C ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hpV).op).hom ((p.app V).hom s)))
    rw [Category.assoc, Scheme.ΓSpecIso_naturality]
    rfl
  ·
    intro c
    have hq : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ ((TopologicalSpace.Opens.map (q ≫ Limits.pullback.snd f sC).base).obj ⊤) := le_top
    have h1 : ((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqW).op).hom ((q.app W).hom (((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)))) = ((q ≫ Limits.pullback.snd f sC).appLE ⊤ ⊤ hq).hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
      rw [← Scheme.Hom.appLE_comp_appLE q (Limits.pullback.snd f sC) ⊤ W ⊤ (hWV.trans le_top) hqW]
      rfl
    rw [h1, appLE_congr_hom hq₂ hq le_top]
    have h2 : (𝟙 (Spec (CommRingCat.of C)) :).appLE ⊤ ⊤ le_top = 𝟙 _ := by
      rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
      erw [Category.id_comp]
      apply CategoryTheory.Functor.map_id _ _
    rw [h2]
    change ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom c = c
    rw [Iso.inv_hom_id]
    rfl


-- created on 2026-10-20
