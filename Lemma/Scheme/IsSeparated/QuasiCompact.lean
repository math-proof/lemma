import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective.lean)
-/
@[path]
private lemma main
    {B : Type u} [CommRing B] {M X : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of B))
    (πX : X ⟶ Spec (CommRingCat.of B)) (π : M ⟶ X) (hπX : π ≫ πX = πM)
    (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
    (hsep : IsSeparated πM) (hqc : QuasiCompact πM) :
    IsSeparated πX ∧ QuasiCompact πX := by
  let _ := hint
  let hπsurj : Surjective π := ⟨hsurj⟩
  let _ := hsep
  let _ := hqc
  constructor
  ·
    let ππ : pullback πM πM ⟶ pullback πX πX :=
      pullback.map πM πM πX πX π π (𝟙 _) ((Category.comp_id _).trans hπX.symm) ((Category.comp_id _).trans hπX.symm)
    have hUC : UniversallyClosed ππ :=
      MorphismProperty.pullbackMap (P := @UniversallyClosed) (inferInstance : UniversallyClosed π)
        (inferInstance : UniversallyClosed π) hπX.symm hπX.symm
    have hS : Surjective ππ :=
      MorphismProperty.pullbackMap (P := @Surjective) hπsurj hπsurj hπX.symm hπX.symm
    have hsq : pullback.diagonal πM ≫ ππ = π ≫ pullback.diagonal πX := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.diagonal_fst,
          Category.id_comp, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.diagonal_snd,
          Category.id_comp, pullback.diagonal_snd, Category.comp_id]
    have hrange : Set.range (pullback.diagonal πX) = ππ '' Set.range (pullback.diagonal πM) := by
      rw [← Set.range_comp]
      change Set.range (pullback.diagonal πX).base = Set.range ((pullback.diagonal πM ≫ ππ).base)
      rw [hsq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hsurj,
        Set.image_univ]
    have hclosed : IsClosed (Set.range (pullback.diagonal πX)) := by
      rw [hrange]
      exact ππ.isClosedMap _ (pullback.diagonal πM).isClosedEmbedding.isClosed_range
    exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩
  ·
    constructor
    intro U hU hUc
    have : πX ⁻¹' U = π '' (πM ⁻¹' U) := by
      rw [← hπX]
      change πX.base ⁻¹' U = π.base '' ((π ≫ πX).base ⁻¹' U)
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq _ hsurj]
    rw [this]
    exact (QuasiCompact.isCompact_preimage U hU hUc).image π.continuous

-- created on 2026-10-20
