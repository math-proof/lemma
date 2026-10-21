import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma appLE_self_eq_id_of_eq_id
  {B : (Scheme : Type (u + 1))} (q : B ⟶ B) (hq : q = 𝟙 B) (U : B.Opens)
  (e : U ≤ (TopologicalSpace.Opens.map q.base).obj U) :
  -- imply
  q.appLE U U e = 𝟙 _ := by
  -- proof
  subst hq
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  rw [Category.id_comp]
  apply B.presheaf.map_id _

private lemma helper_main
  {X B Y : (Scheme : Type (u + 1))} (p : X ⟶ B) (ε : B ⟶ X) (hε : ε ≫ p = 𝟙 B)
  (hp : IsClosedMap p)
  (hH0 : ∀ U : B.Opens, IsAffineOpen U → Function.Surjective (p.app U))
  (f : X ⟶ Y) (hf : ∀ x : X, f (ε (p x)) = f x) :
  -- imply
  p ≫ ε ≫ f = f := by
  -- proof
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := f x) (U := ⊤) trivial
  have hC : IsClosed (p '' ((((TopologicalSpace.Opens.map f.base).obj V : Set X)ᶜ))) :=
    hp _ (((TopologicalSpace.Opens.map f.base).obj V).isOpen.isClosed_compl)
  have hbC : p x ∈ (⟨(p '' (((TopologicalSpace.Opens.map f.base).obj V : Set X)ᶜ))ᶜ, hC.isOpen_compl⟩ : B.Opens) := by
    rintro ⟨x', hx', e⟩
    apply hx'
    change f x' ∈ V
    rw [← hf x', e, hf x]
    apply hxV
  obtain ⟨U, hU, hbU, hUC⟩ := exists_isAffineOpen_mem_and_subset hbC
  have e₁ : (TopologicalSpace.Opens.map p.base).obj U ≤ (TopologicalSpace.Opens.map f.base).obj V := by
    intro x' hx'
    by_contra h
    apply hUC hx' ⟨x', h, rfl⟩
  have e₂ : (TopologicalSpace.Opens.map p.base).obj U ≤ (TopologicalSpace.Opens.map (p ≫ ε ≫ f).base).obj V := by
    intro x' hx'
    change (p ≫ ε ≫ f) x' ∈ V
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hf]
    apply e₁ hx'
  refine ⟨(TopologicalSpace.Opens.map p.base).obj U, hbU, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι _ e₂, ← Scheme.Hom.resLE_comp_ι _ e₁]
  congr 1
  let _ : IsAffine V := hV
  apply ext_of_isAffine
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  congr 2
  have e₄ : U ≤ (TopologicalSpace.Opens.map ε.base).obj ((TopologicalSpace.Opens.map p.base).obj U) := by
    intro b hb
    change p (ε b) ∈ U
    rwa [← Scheme.Hom.comp_apply, hε]
  have key : p.app U ≫ ε.appLE ((TopologicalSpace.Opens.map p.base).obj U) U e₄ = 𝟙 _ := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    apply appLE_self_eq_id_of_eq_id _ hε _ _
  have dec : (p ≫ ε ≫ f).appLE V ((TopologicalSpace.Opens.map p.base).obj U) e₂ = f.appLE V ((TopologicalSpace.Opens.map p.base).obj U) e₁ ≫ ε.appLE ((TopologicalSpace.Opens.map p.base).obj U) U e₄ ≫ p.app U := by
    rw [Scheme.Hom.app_eq_appLE p, Scheme.Hom.appLE_comp_appLE_assoc ε f, Scheme.Hom.appLE_comp_appLE p (ε ≫ f)]
  rw [dec]
  set θ := ε.appLE ((TopologicalSpace.Opens.map p.base).obj U) U e₄ ≫ p.app U with hθ
  have hθid : θ = 𝟙 _ := by
    ext t
    obtain ⟨r, rfl⟩ := hH0 U hU t
    change (p.app U ≫ θ) r = p.app U r
    rw [hθ, ← Category.assoc, key, Category.id_comp]
  rw [hθid, Category.comp_id]

/--
[AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app.lean)
-/
@[path]
private lemma main
  {X B Y : (Scheme : Type (u + 1))} (p : X ⟶ B) (ε : B ⟶ X) (hε : ε ≫ p = 𝟙 B)
  (hp : IsClosedMap p)
  (hH0 : ∀ U : B.Opens, IsAffineOpen U → Function.Surjective (p.app U))
  (f : X ⟶ Y) (hf : ∀ x : X, f (ε (p x)) = f x) :
  -- imply
  p ≫ ε ≫ f = f :=
  helper_main p ε hε hp hH0 f hf


-- created on 2026-10-20
