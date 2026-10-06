import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

/--
[AlgebraicGeometry_Proj_hom_ext_of_forall_exists_basicOpen](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Proj_hom_ext_of_forall_exists_basicOpen.lean)
-/
@[main]
private lemma main
  {A : Type u} [CommRing A]
  {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {W : Scheme.{u}}
  {a b : W ⟶ Proj 𝒜}
-- given
  (h : ∀ w : W, ∃ (n : ℕ) (r : A) (hn : 0 < n) (hr : r ∈ 𝒜 n) (e : a ⁻¹ᵁ Proj.basicOpen 𝒜 r = b ⁻¹ᵁ Proj.basicOpen 𝒜 r), w ∈ a ⁻¹ᵁ Proj.basicOpen 𝒜 r ∧ ∀ x : Away 𝒜 r, a.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl (Proj.awayToSection 𝒜 r x) = b.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le (Proj.awayToSection 𝒜 r x)) :
-- imply
  a = b := by
-- proof
  refine Scheme.hom_ext_of_forall a b fun w => ?_
  obtain ⟨n, r, hn, hr, e, hw, happ⟩ := h w
  refine ⟨a ⁻¹ᵁ Proj.basicOpen 𝒜 r, hw, ?_⟩
  have hsurj : Function.Surjective (Proj.awayToSection 𝒜 r) := by
    rw [← Proj.basicOpenIsoAway_hom 𝒜 r hr hn]
    exact (ConcreteCategory.bijective_of_isIso _).2
  have happLE : a.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl =
      b.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le := by
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    exact happ y
  have key : a.resLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl =
      b.resLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le := by
    haveI : IsAffine (Proj.basicOpen 𝒜 r).toScheme := Proj.isAffineOpen_basicOpen 𝒜 r hr hn
    apply ext_of_isAffine
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, happLE]
  have e₁ := Scheme.Hom.resLE_comp_ι a (U := Proj.basicOpen 𝒜 r) (V := a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl
  have e₂ := Scheme.Hom.resLE_comp_ι b (U := Proj.basicOpen 𝒜 r) (V := a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le
  rw [← e₁, ← e₂, key]


-- created on 2026-10-05
