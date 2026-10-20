import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_iff_apply_closedPoint_mem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_iff_apply_closedPoint_mem_range.lean)
-/
@[path]
private lemma main
  {X Z : Scheme} {i : Z ⟶ X} [IsClosedImmersion i]
  {K : Type u} [Field K]
  {x : Spec (CommRingCat.of K) ⟶ X} :
-- imply
  (∃ z : Spec (CommRingCat.of K) ⟶ Z, z ≫ i = x) ↔
    x.base (IsLocalRing.closedPoint K) ∈ Set.range i.base := by
-- proof
  constructor
  ·
    rintro ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    refine ⟨_, rfl⟩
  ·
    intro hmem
    have hpt : ∀ p : ↥(Spec (CommRingCat.of K)), p = IsLocalRing.closedPoint K := fun p =>
      ((PrimeSpectrum.instUnique (R := (CommRingCat.of K))).uniq p).trans
        ((PrimeSpectrum.instUnique (R := (CommRingCat.of K))).uniq (IsLocalRing.closedPoint K)).symm
    have hsurj : Surjective (pullback.fst x i) := by
      refine ⟨fun p => ?_⟩
      obtain ⟨y, hy⟩ := hmem
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := i)
        (IsLocalRing.closedPoint K) y hy.symm
      refine ⟨w, ?_⟩
      rw [hpt p]
      refine hw
    have : IsIso (pullback.fst x i) := isIso_of_isClosedImmersion_of_surjective _
    refine ⟨inv (pullback.fst x i) ≫ pullback.snd x i, ?_⟩
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]


-- created on 2026-10-20
