import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

/--
[AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq.lean)
-/
@[main]
private lemma main
  {P P' : Scheme.{u}}
  {β : P' ⟶ P}
  {U : P.Opens}
  {s : (U : Scheme.{u}) ⟶ P'} [IsOpenImmersion s]
-- given
  (hsβ : s ≫ β = U.ι)
  (hsr : Set.range s.base = β.base ⁻¹' (U : Set P)) :
-- imply
  IsIso (β ∣_ U) := by
-- proof
  have hr : Set.range s.base = Set.range (β ⁻¹ᵁ U).ι.base := by
    rw [hsr, Scheme.Opens.range_ι]; rfl
  let e := IsOpenImmersion.isoOfRangeEq s (β ⁻¹ᵁ U).ι hr
  have he : e.hom ≫ (β ⁻¹ᵁ U).ι = s := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h1 : e.hom ≫ (β ∣_ U) = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, he, hsβ,
      Category.id_comp]
  have h2 : β ∣_ U = e.inv := by
    rw [← Category.id_comp (β ∣_ U), ← e.inv_hom_id, Category.assoc, h1, Category.comp_id]
  rw [h2]
  infer_instance


-- created on 2026-10-05
