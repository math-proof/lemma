import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry


/--
[adjunction_counit_isIso_of_conservative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjointEquivalence.lean)
-/
@[path]
lemma adjunction_counit_isIso_of_conservative
  {C : Type u}
  [Category.{v} C]
  {D : Type u}
  [Category.{v} D]
  {F : C ⥤ D}
  {G : D ⥤ C}
  {adj : F ⊣ G}
  [F.Full]
  [F.Faithful]
  [G.ReflectsIsomorphisms]
  {X : D} :
-- imply
  IsIso (adj.counit.app X) := by
-- proof
  have : IsIso (G.map (adj.counit.app X)) :=
    NatIso.isIso_app_of_isIso (whiskerRight adj.counit G) X
  exact isIso_of_reflects_iso (adj.counit.app X) G
section AffineMorphisms

/--
[Spec_isAffine'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjointEquivalence.lean)
-/
@[path]
lemma Spec_isAffine'
  {R : CommRingCat} :
-- imply
  IsAffine (Spec R) :=
-- proof
  isAffine_Spec R
end AffineMorphisms
section RestrictScalarsFull

/--
[restrictScalars_full_of_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjointEquivalence.lean)
-/
@[path]
lemma restrictScalars_full_of_surjective
  [Ring R]
  [Ring S]
  {f : R →+* S}
-- given
  (hf : Function.Surjective f) :
-- imply
  (ModuleCat.restrictScalars f).Full where map_surjective {M N} g := by
-- proof
  refine ⟨ModuleCat.ofHom ⟨g.hom.toAddHom, fun s m => ?_⟩, ?_⟩
  · obtain ⟨r, rfl⟩ := hf s
    change g.hom (f r • m) = f r • g.hom m
    have := g.hom.map_smul r m
    simp only [ModuleCat.restrictScalars.smul_def] at this
    exact this
  · rfl
end RestrictScalarsFull
section RestrictScalarsEssImage

/--
[restrictScalars_essImage_annihilated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjointEquivalence.lean)
-/
@[path]
lemma restrictScalars_essImage_annihilated
  [CommRing R]
  {I : Ideal R}
  {M : ModuleCat R}
-- given
  (h : ∃ (N : ModuleCat (R ⧸ I)), Nonempty ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N ≅ M)) :
-- imply
  ∀ (r : R) (m : M), r ∈ I → r • m = 0 := by
-- proof
  rintro r m hr
  obtain ⟨N, ⟨iso⟩⟩ := h
  have key : r • (iso.inv.hom m) =
    (0 : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N) := by
    change (Ideal.Quotient.mk I r) • (iso.inv.hom m : N) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  have h1 := iso.hom.hom.map_smul r (iso.inv.hom m)
  rw [key, map_zero] at h1
  have h2 : iso.hom.hom (iso.inv.hom m) = m := by
    change (iso.inv ≫ iso.hom).hom m = m
    simp [iso.inv_hom_id]
  rw [h2] at h1; exact h1.symm

/--
[restrictScalars_essImage_of_annihilated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjointEquivalence.lean)
-/
@[path]
lemma restrictScalars_essImage_of_annihilated
  [CommRing R]
  {I : Ideal R}
  {M : ModuleCat R}
-- given
  (hann : ∀ (r : R) (m : M), r ∈ I → r • m = 0) :
-- imply
  ∃ (N : ModuleCat (R ⧸ I)), Nonempty ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N ≅ M) := by
-- proof
  have htors : Module.IsTorsionBySet R M (I : Set R) := by
    intro m ⟨a, ha⟩; exact hann a m ha
  letI := htors.module
  let N : ModuleCat (R ⧸ I) := ModuleCat.of (R ⧸ I) M
  exact ⟨N, ⟨{
    hom := ModuleCat.ofHom LinearMap.id
    inv := ModuleCat.ofHom LinearMap.id
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl }⟩⟩
end RestrictScalarsEssImage


-- created on 2026-10-23
