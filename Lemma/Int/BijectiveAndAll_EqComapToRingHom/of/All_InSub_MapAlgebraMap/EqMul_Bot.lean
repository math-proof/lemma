import Mathlib
import sympy.Basic


/--
[AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot.lean)
-/
@[path]
private lemma main
  {T' : Type u} [CommRing T']
  {I : Ideal T'}
  {C : Type u} [CommRing C] [Algebra T' C]
  {ψ : C →ₐ[T'] C}
-- given
  (hI2 : I * I = ⊥)
  (hψ : ∀ c : C, ψ c - c ∈ I.map (algebraMap T' C)) :
-- imply
  Function.Bijective ψ ∧ ∀ p : PrimeSpectrum C, PrimeSpectrum.comap ψ.toRingHom p = p := by
-- proof
  classical
  set J : Ideal C := I.map (algebraMap T' C) with hJ
  have hJJ : J * J = ⊥ := by rw [hJ, ← Ideal.map_mul, hI2, Ideal.map_bot]
  have hmul0 : ∀ y ∈ J, ∀ z ∈ J, y * z = 0 := fun y hy z hz => by
    have := Ideal.mul_mem_mul hy hz; rwa [hJJ, Ideal.mem_bot] at this

  have hfix : ∀ y ∈ J, ψ y = y := by
    intro y hy
    rw [hJ, Ideal.map] at hy
    refine Submodule.span_induction (p := fun y _ => ψ y = y) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, rfl⟩
      exact ψ.commutes i
    · exact map_zero ψ
    · intro y z _ _ hy hz
      rw [map_add, hy, hz]
    · intro c y hy' hy
      have hyJ : y ∈ J := by rw [hJ, Ideal.map]; exact hy'
      rw [smul_eq_mul, map_mul, hy, ← sub_eq_zero, ← sub_mul]
      exact hmul0 _ (hψ c) _ hyJ
  refine ⟨?_, ?_⟩
  ·
    refine Function.bijective_iff_has_inverse.mpr ⟨fun c => c - (ψ c - c), fun c => ?_, fun c => ?_⟩
    · show ψ c - (ψ (ψ c) - ψ c) = c
      have : ψ (ψ c) = ψ c + (ψ c - c) := by
        conv_lhs => rw [show ψ c = c + (ψ c - c) by abel]
        rw [map_add, hfix _ (hψ c)]
      rw [this]; abel
    · show ψ (c - (ψ c - c)) = c
      rw [map_sub, hfix _ (hψ c)]; abel
  · intro p
    apply PrimeSpectrum.ext
    ext c
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hnil : ψ c - c ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [pow_two, hmul0 _ (hψ c) _ (hψ c)]
      exact p.asIdeal.zero_mem
    constructor
    · intro h
      have := p.asIdeal.sub_mem h hnil
      rwa [show (ψ.toRingHom c) - (ψ c - c) = c from by simp] at this
    · intro h
      have := p.asIdeal.add_mem h hnil
      rwa [show c + (ψ c - c) = ψ.toRingHom c from by simp] at this


-- created on 2026-10-09
