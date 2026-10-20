import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[Ideal_map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx.lean)
-/
@[path]
private lemma main
    {R S F : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S] [Field F]
    [Algebra R S] [Module.IsTorsionFree R S] [Algebra S F] [IsFractionRing S F]
    (p : Ideal R) (hp : p ≠ ⊥) (𝔓 : Ideal S) [𝔓.IsMaximal] [𝔓.LiesOver p]
    (P : ValuationSubring F)
    (hSP : ∀ s : S, algebraMap S F s ∈ P)
    (hcent : ∀ s : S, algebraMap S F s ∈ P.nonunits ↔ s ∈ 𝔓)
    (hfrac : ∀ e : ↥P, ∃ s t : S, t ∉ 𝔓 ∧ (e : F) * algebraMap S F t = algebraMap S F s)
    (φ : R →+* ↥P) (hφ : ∀ r : R, ((φ r : ↥P) : F) = algebraMap S F (algebraMap R S r)) :
    Ideal.map φ p = IsLocalRing.maximalIdeal ↥P ^ Ideal.ramificationIdx' p 𝔓 := by
  classical
  let ψ : S →+* ↥P := (algebraMap S F).codRestrict P hSP
  have hψ : ∀ s : S, ((ψ s : ↥P) : F) = algebraMap S F s := fun s => rfl
  let algSP : Algebra S ↥P := ψ.toAlgebra
  let algRP : Algebra R ↥P := φ.toAlgebra
  let _ : IsScalarTower R S ↥P := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    change ((φ r : ↥P) : F) = ((ψ (algebraMap R S r) : ↥P) : F)
    rw [hψ, hφ]
  have hunit : ∀ {t : S}, t ∉ 𝔓 → IsUnit (ψ t) := by
    intro t ht
    by_contra h
    have : (ψ t : ↥P) ∈ maximalIdeal ↥P := h
    rw [← P.coe_mem_nonunits_iff, hψ] at this
    exact ht ((hcent t).mp this)
  let _ : IsLocalization.AtPrime ↥P 𝔓 := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨t, ht⟩
      exact hunit ht
    · intro e
      obtain ⟨s, t, ht, hst⟩ := hfrac e
      refine ⟨⟨s, ⟨t, ht⟩⟩, Subtype.ext ?_⟩
      change (e : F) * ((ψ t : ↥P) : F) = ((ψ s : ↥P) : F)
      rw [hψ, hψ]; exact hst
    · intro s₁ s₂ h
      have h' : algebraMap S F s₁ = algebraMap S F s₂ := congrArg (fun x : ↥P => (x : F)) h
      exact ⟨1, by simpa using IsFractionRing.injective S F h'⟩
  have h𝔓0 : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝔓
  let _ : IsDiscreteValuationRing ↥P :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S h𝔓0 ↥P
  have hmap𝔓 : Ideal.map (algebraMap S ↥P) 𝔓 = maximalIdeal ↥P :=
    IsLocalization.AtPrime.map_eq_maximalIdeal 𝔓 ↥P
  have hm0 : maximalIdeal ↥P ≠ ⊥ := IsDiscreteValuationRing.not_a_field ↥P
  have he1 : Ideal.ramificationIdx' 𝔓 (maximalIdeal ↥P) = 1 := by
    apply Ideal.ramificationIdx_spec
    · rw [pow_one, hmap𝔓]
    · rw [hmap𝔓]
      intro hle
      have hlt := Ideal.pow_succ_lt_pow hm0 1
      rw [pow_one] at hlt
      exact (lt_irrefl _) (lt_of_le_of_lt hle hlt)
  have hψinj : Function.Injective (algebraMap S ↥P) := by
    intro a b h
    exact IsFractionRing.injective S F (congrArg (fun x : ↥P => (x : F)) h)
  have hpS : Ideal.map (algebraMap R S) p ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  have hfg : Ideal.map (algebraMap R ↥P) p ≠ ⊥ := by
    rw [IsScalarTower.algebraMap_eq R S ↥P, ← Ideal.map_map]
    exact fun h => hpS ((Ideal.map_eq_bot_iff_of_injective hψinj).mp h)
  have hg0 : Ideal.map (algebraMap S ↥P) 𝔓 ≠ ⊥ := by rw [hmap𝔓]; exact hm0
  have hg : Ideal.map (algebraMap S ↥P) 𝔓 ≤ maximalIdeal ↥P := hmap𝔓.le
  have htower := Ideal.ramificationIdx_algebra_tower (p := p) (P := 𝔓) (Q := maximalIdeal ↥P) hg0 hfg hg
  rw [he1, mul_one] at htower
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥P
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hfg hϖ
  have hmax : maximalIdeal ↥P = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hn' : Ideal.map (algebraMap R ↥P) p = maximalIdeal ↥P ^ n := by
    rw [hn, hmax, Ideal.span_singleton_pow]
  have hidx : Ideal.ramificationIdx' p (maximalIdeal ↥P) = n := by
    apply Ideal.ramificationIdx_spec
    · exact hn'.le
    · rw [hn']
      intro hle
      exact (lt_irrefl _) (lt_of_le_of_lt hle (Ideal.pow_succ_lt_pow hm0 n))
  change Ideal.map (algebraMap R ↥P) p = _
  rw [hn', ← htower, hidx]

-- created on 2026-10-20
