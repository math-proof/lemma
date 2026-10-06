import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_denseRange_of_comp_eq.lean)
-/
@[main]
private lemma main
  {W X Y Z : Scheme.{u}} [IsReduced X]
  {g : W ⟶ X}
  {ι : Z ⟶ Y} [IsClosedImmersion ι]
  {φ : X ⟶ Y}
  {ψ : W ⟶ Z}
-- given
  (hg : DenseRange g.base)
  (hψ : ψ ≫ ι = g ≫ φ) :
-- imply
  ∃! χ : X ⟶ Z, χ ≫ ι = φ := by
-- proof
  classical

  let j : pullback ι φ ⟶ X := pullback.snd ι φ
  haveI : IsClosedImmersion j := inferInstance
  have hrange : Set.range g.base ⊆ Set.range j.base := by
    rintro _ ⟨w, rfl⟩

    obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := ι) (g := φ) (ψ.base w) (g.base w)
      (by
        change (ψ ≫ ι).base w = (g ≫ φ).base w
        rw [hψ])
    exact ⟨t, ht2⟩

  haveI : Surjective j := ⟨by
    rw [← Set.range_eq_univ]
    have hcl : IsClosed (Set.range j.base) := j.isClosedEmbedding.isClosed_range
    exact Set.eq_univ_of_univ_subset ((hg.closure_eq ▸ closure_minimal hrange hcl).ge)⟩
  haveI : IsIso j := isIso_of_isClosedImmersion_of_surjective j
  refine ⟨inv j ≫ pullback.fst ι φ, ?_, ?_⟩
  · show (inv j ≫ pullback.fst ι φ) ≫ ι = φ
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · intro χ hχ
    exact (cancel_mono ι).mp (by rw [hχ, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc])


-- created on 2026-10-05
