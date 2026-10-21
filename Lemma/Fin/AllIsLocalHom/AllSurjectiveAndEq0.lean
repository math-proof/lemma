import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsLocalRing_exists_jointly_injective_isLocalHom_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_jointly_injective_isLocalHom_of_isReduced.lean)
-/
@[path]
private lemma main
  (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsReduced T] :
  -- imply
  ∃ (n : ℕ) (A : Fin n → Type) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsDomain (A i)) (_ : ∀ i, IsLocalRing (A i)) (_ : ∀ i, IsNoetherianRing (A i)) (χ : ∀ i, RingHom T (A i)), (∀ i, IsLocalHom (χ i)) ∧ (∀ i, Function.Surjective (χ i)) ∧ ∀ x : T, (∀ i, χ i x = 0) → x = 0 := by
  -- proof
  classical
  have hfin := minimalPrimes.finite_of_isNoetherianRing T
  set s := hfin.toFinset with hs
  let e := s.equivFin
  let 𝔭 : Fin s.card → Ideal T := fun i => (e.symm i).1
  have h𝔭 : ∀ i, 𝔭 i ∈ minimalPrimes T := fun i => hfin.mem_toFinset.mp (e.symm i).2
  have hprime : ∀ i, (𝔭 i).IsPrime := fun i => Ideal.IsMinimalPrime.isPrime (h𝔭 i)
  have hdom : ∀ i, IsDomain (T ⧸ 𝔭 i) := fun i => by
    let _ := hprime i
    infer_instance
  have hloc : ∀ i, IsLocalRing (T ⧸ 𝔭 i) := fun i => by
    let _ := hdom i
    apply IsLocalRing.of_surjective' (Ideal.Quotient.mk (𝔭 i)) Ideal.Quotient.mk_surjective
  refine ⟨s.card, fun i => T ⧸ 𝔭 i, inferInstance, hdom, hloc, fun i => inferInstance, fun i => Ideal.Quotient.mk (𝔭 i),
    fun i => ?_, fun i => Ideal.Quotient.mk_surjective, ?_⟩
  ·
    let _ := hdom i
    let _ := hloc i
    apply IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  ·
    intro x hx
    have hmem : x ∈ sInf (minimalPrimes T) := by
      rw [Ideal.mem_sInf]
      intro J hJ
      have hJs : J ∈ s := hfin.mem_toFinset.mpr hJ
      have hi : 𝔭 (e ⟨J, hJs⟩) = J := by
        show (e.symm (e ⟨J, hJs⟩)).1 = J
        rw [Equiv.symm_apply_apply]
      rw [← hi]
      apply Ideal.Quotient.eq_zero_iff_mem.mp (hx _)
    have hbot : sInf (minimalPrimes T) = ⊥ := by
      rw [minimalPrimes, Ideal.sInf_minimalPrimes]
      apply nilradical_eq_zero T
    rw [hbot] at hmem
    apply hmem


-- created on 2026-10-20
