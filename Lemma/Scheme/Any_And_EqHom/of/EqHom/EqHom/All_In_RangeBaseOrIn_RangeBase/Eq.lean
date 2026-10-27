import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry


private lemma ker_eq_vanishingIdeal {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) :
  f.ker = Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure (Set.range f.base)) := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot (X := X),
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  simp [Set.image_univ]

private lemma image_eq_of_forall_mem_or {α : Type u} [TopologicalSpace α] (e : α ≃ₜ α) (Z₁ Z₂ : Set α)
  (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (hirr : IsPreirreducible Z₂)
  (hcover : ∀ z, z ∈ Z₁ ∨ z ∈ Z₂) (hfix : ∀ z ∈ Z₁, e z = z) : e '' Z₂ = Z₂ := by
  have key : ∀ (g : α ≃ₜ α), (∀ z ∈ Z₁, g z = z) → g '' Z₂ ⊆ Z₂ ∨ (∀ z ∈ Z₂, g z = z) := by
    intro g hg
    have hirr' : IsPreirreducible (g '' Z₂) := hirr.image g g.continuous.continuousOn
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hirr') Z₁ Z₂ hZ₁ hZ₂
      (by rintro _ ⟨z, hz, rfl⟩; exact hcover _) with h | h
    ·
      right
      intro z hz
      have h1 : g z ∈ Z₁ := h ⟨z, hz, rfl⟩
      have h2 : g (g z) = g z := hg _ h1
      refine g.injective h2
    ·
      left; exact h
  obtain h | h := key e hfix
  ·
    refine subset_antisymm h ?_
    have hfix' : ∀ z ∈ Z₁, e.symm z = z := fun z hz => by
      rw [Homeomorph.symm_apply_eq]; exact (hfix z hz).symm
    obtain h' | h' := key e.symm hfix'
    ·
      intro z hz
      exact ⟨e.symm z, h' ⟨z, hz, rfl⟩, e.apply_symm_apply z⟩
    ·
      intro z hz
      refine ⟨z, hz, ?_⟩
      have := h' z hz
      rw [Homeomorph.symm_apply_eq] at this
      apply this.symm
  ·
    ext y
    constructor
    ·
      rintro ⟨z, hz, rfl⟩; rwa [h z hz]
    ·
      intro hy; exact ⟨y, hy, h y hy⟩
/--
[AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_comp_hom_eq_of_isClosedImmersion_of_forall_mem_range_or](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_comp_hom_eq_of_isClosedImmersion_of_forall_mem_range_or.lean)
-/
@[path]
private lemma main
  {X C₁ C₂ S : Scheme.{u}} [IsIntegral C₂]
  {x : X ⟶ S}
  {c₂ : C₂ ⟶ S}
  {i₁ : C₁ ⟶ X} [IsClosedImmersion i₁]
  {i₂ : C₂ ⟶ X} [IsClosedImmersion i₂]
  {w : X ≅ X}
-- given
  (hi₂ : i₂ ≫ x = c₂)
  (hcover : ∀ z : X, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
  (hw : w.hom ≫ x = x)
  (hfix : i₁ ≫ w.hom = i₁) :
-- imply
  ∃ α₂ : C₂ ≅ C₂, α₂.hom ≫ c₂ = c₂ ∧ α₂.hom ≫ i₂ = i₂ ≫ w.hom := by
-- proof
  classical
    let e : ↥X ≃ₜ ↥X := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso w)
    have he : ∀ z, e z = w.hom.base z := fun z => rfl
    have hfix' : ∀ z ∈ Set.range i₁.base, e z = z := by
      rintro _ ⟨c, rfl⟩
      have h := Scheme.Hom.comp_apply i₁ w.hom c
      rw [hfix] at h
      apply h.symm
    have hZ₁ : IsClosed (Set.range i₁.base) := i₁.isClosedEmbedding.isClosed_range
    have hZ₂ : IsClosed (Set.range i₂.base) := i₂.isClosedEmbedding.isClosed_range
    have hirr : IsPreirreducible (Set.range i₂.base) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ (X := ↥C₂)).isPreirreducible.image _ i₂.base.hom.continuous.continuousOn
    have himg : w.hom.base '' Set.range i₂.base = Set.range i₂.base :=
      image_eq_of_forall_mem_or e _ _ hZ₁ hZ₂ hirr hcover hfix'
    have hrange : Set.range (i₂ ≫ w.hom).base = Set.range i₂.base := by
      have hc : ⇑(i₂ ≫ w.hom).base = w.hom.base ∘ i₂.base := funext fun c => Scheme.Hom.comp_apply i₂ w.hom c
      rw [hc, Set.range_comp, himg]
    have hker : i₂.ker = (i₂ ≫ w.hom).ker := by
      rw [ker_eq_vanishingIdeal, ker_eq_vanishingIdeal, hrange]
    have : IsClosedImmersion (i₂ ≫ w.hom) := inferInstance
    have := IsClosedImmersion.isIso_lift i₂ (i₂ ≫ w.hom) hker
    refine ⟨asIso (IsClosedImmersion.lift i₂ (i₂ ≫ w.hom) hker.le), ?_, ?_⟩
    · rw [asIso_hom, ← hi₂, ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, hw]
    · rw [asIso_hom, IsClosedImmersion.lift_fac]


-- created on 2026-10-23
