import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R]
  {S : Type v} [CommRing S] [IsLocalRing S] [IsDomain S] [IsIntegrallyClosed S]
  (f : RingHom R S) [IsLocalHom f]
  -- given
  (hf : f.Flat) :
  -- imply
  IsDomain R ∧ IsIntegrallyClosed R := by
  -- proof
  algebraize [f]
  let hff : Module.FaithfullyFlat R S :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ inferInstance ‹_›
  have hinj : Function.Injective (algebraMap R S) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hff).injective
  let _ : IsDomain R := hinj.isDomain _
  refine ⟨inferInstance, ?_⟩
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  let φ : RingHom (FractionRing R) (FractionRing S) :=
    IsFractionRing.map (A := R) (B := S) (K := FractionRing R) (L := FractionRing S) (j := algebraMap R S) hinj
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap S (FractionRing S) (algebraMap R S r) := by
    intro r
    simp [φ, IsFractionRing.map]
  have hx' : IsIntegral S (φ (algebraMap R _ a / algebraMap R _ b)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (algebraMap R S), hp.map _, ?_⟩
    have hcomp : φ.comp (algebraMap R (FractionRing R)) = (algebraMap S (FractionRing S)).comp (algebraMap R S) :=
      RingHom.ext hφ
    rw [Polynomial.eval₂_map, ← hcomp, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨s, hs⟩ := (isIntegrallyClosed_iff (FractionRing S)).mp ‹IsIntegrallyClosed S› hx'
  have hfb0 : algebraMap R S b ≠ 0 := fun h => hb0 (hinj (by simpa using h))
  have hdiv : algebraMap R S a = s * algebraMap R S b := by
    have h1 : algebraMap S (FractionRing S) s =
        algebraMap S (FractionRing S) (algebraMap R S a) / algebraMap S (FractionRing S) (algebraMap R S b) := by
      rw [hs, map_div₀, hφ, hφ]
    have h2 : algebraMap S (FractionRing S) (algebraMap R S b) ≠ 0 := by
      simpa using hfb0
    apply IsFractionRing.injective S (FractionRing S)
    rw [map_mul, h1, div_mul_cancel₀ _ h2]
  have hmem : a ∈ Ideal.comap (algebraMap R S) ((Ideal.span {b}).map (algebraMap R S)) := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, hdiv]
    apply Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton (algebraMap R S b)))
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨r, ?_⟩
  have : algebraMap R (FractionRing R) b ≠ 0 := by
    simpa using hb0
  rw [eq_div_iff this, ← map_mul, hr]


-- created on 2026-10-20
