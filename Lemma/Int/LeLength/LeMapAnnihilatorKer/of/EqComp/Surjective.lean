import Mathlib
import sympy.Basic


/--
[AlgHom_length_cotangent_le_and_congruenceIdeal_le_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_length_cotangent_le_and_congruenceIdeal_le_of_surjective.lean)
-/
@[main]
private lemma main
  [CommRing 𝒪] [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
  {φ : R →ₐ[𝒪] T}
  {πR : R →ₐ[𝒪] 𝒪}
  {πT : T →ₐ[𝒪] 𝒪}
-- given
  (hφ : Function.Surjective φ)
  (hπ : πT.comp φ = πR) :
-- imply
  Module.length 𝒪 (RingHom.ker πT).Cotangent ≤ Module.length 𝒪 (RingHom.ker πR).Cotangent ∧
      (RingHom.ker πR).annihilator.map πR ≤ (RingHom.ker πT).annihilator.map πT := by
-- proof
  have hmem : ∀ r, r ∈ RingHom.ker πR ↔ φ r ∈ RingHom.ker πT := fun r => by
    rw [RingHom.mem_ker, RingHom.mem_ker, ← AlgHom.congr_fun hπ r]; rfl
  have hcomap : RingHom.ker πR ≤ (RingHom.ker πT).comap φ := fun r hr =>
    Ideal.mem_comap.mpr ((hmem r).mp hr)
  constructor
  · refine Module.length_le_of_surjective (Ideal.mapCotangent _ _ φ hcomap) ?_
    intro m
    obtain ⟨⟨t, ht⟩, rfl⟩ := (RingHom.ker πT).toCotangent_surjective m
    obtain ⟨r, rfl⟩ := hφ t
    exact ⟨(RingHom.ker πR).toCotangent ⟨r, (hmem r).mpr ht⟩, by simp⟩
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    rw [Ideal.mem_comap, show πR x = πT (φ x) from (AlgHom.congr_fun hπ x).symm]
    refine Ideal.mem_map_of_mem _ ?_
    rw [Submodule.mem_annihilator] at hx ⊢
    intro t ht
    obtain ⟨r, rfl⟩ := hφ t
    rw [smul_eq_mul, ← map_mul, ← smul_eq_mul, hx r ((hmem r).mpr ht), map_zero]


-- created on 2026-10-05
