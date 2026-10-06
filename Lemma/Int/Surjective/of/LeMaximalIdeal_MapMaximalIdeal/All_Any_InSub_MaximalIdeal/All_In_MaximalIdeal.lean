import Mathlib
import sympy.Basic


/--
[IsLocalRing_surjective_of_isAdicComplete_of_maximalIdeal_le_map_sup_sq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_surjective_of_isAdicComplete_of_maximalIdeal_le_map_sup_sq.lean)
-/
@[main]
private lemma main
  {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
  {f : R →+* S}
-- given
  (hloc : ∀ r ∈ IsLocalRing.maximalIdeal R, f r ∈ IsLocalRing.maximalIdeal S)
  (hres : ∀ s : S, ∃ r : R, s - f r ∈ IsLocalRing.maximalIdeal S)
  (hcot : IsLocalRing.maximalIdeal S ≤ (IsLocalRing.maximalIdeal R).map f ⊔ IsLocalRing.maximalIdeal S ^ 2) :
-- imply
  Function.Surjective f := by
-- proof
  classical
  have hmap_le : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact hloc r hr
  have heq : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map f := by
    refine le_antisymm ?_ hmap_le
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal S)
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _)
    rw [Ideal.smul_eq_mul, ← pow_two]
    exact hcot
  haveI : IsHausdorff ((IsLocalRing.maximalIdeal R).map f) S := by rw [← heq]; infer_instance
  apply surjective_of_mk_map_comp_surjective (I := IsLocalRing.maximalIdeal R) f
  intro y
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := hres s
  refine ⟨r, ?_⟩
  rw [RingHom.comp_apply, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← heq]
  exact hr


-- created on 2026-10-05
