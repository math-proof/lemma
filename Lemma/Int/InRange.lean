import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v u' v'

/--
[IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
  {S : Type v} [CommRing S] [IsLocalRing S] [IsDomain S]
  (f : RingHom R S) [IsLocalHom f]
  (K : Type u') [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type v') [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  (x : K)
  -- given
  (hf : f.Flat)
  (hcomm : ∀ r : R, algebraMap R L r = algebraMap S L (f r))
  (hx : algebraMap K L x ∈ (algebraMap S L).range) :
  -- imply
  x ∈ (algebraMap R K).range := by
  -- proof
  algebraize [f]
  let hff : Module.FaithfullyFlat R S :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ inferInstance ‹_›
  have hinj : Function.Injective (algebraMap R S) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hff).injective
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨s, hs⟩ := hx
  have hKL : ∀ r : R, algebraMap K L (algebraMap R K r) = algebraMap S L (algebraMap R S r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply R K L r, hcomm r]
    rfl
  have hfb0 : algebraMap R S b ≠ 0 := fun h => hb0 (hinj (by rw [h, map_zero]))
  have hdiv : algebraMap R S a = s * algebraMap R S b := by
    have h1 : algebraMap S L s =
        algebraMap S L (algebraMap R S a) / algebraMap S L (algebraMap R S b) := by
      rw [hs, map_div₀, hKL, hKL]
    have h2 : algebraMap S L (algebraMap R S b) ≠ 0 := fun h =>
      hfb0 ((IsFractionRing.to_map_eq_zero_iff (K := L)).mp h)
    apply IsFractionRing.injective S L
    rw [map_mul, h1, div_mul_cancel₀ _ h2]
  have hmem : a ∈ Ideal.comap (algebraMap R S) ((Ideal.span {b}).map (algebraMap R S)) := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, hdiv]
    apply Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton (algebraMap R S b)))
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨r, ?_⟩
  have hbK : algebraMap R K b ≠ 0 := fun h => hb0 ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h)
  rw [eq_div_iff hbK, ← map_mul, hr]


-- created on 2026-10-20
