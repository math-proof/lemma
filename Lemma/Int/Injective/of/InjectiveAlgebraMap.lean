import Mathlib
import sympy.Basic


/--
[Algebra_IsIntegral_injective_of_injective_algebraMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsIntegral_injective_of_injective_algebraMap.lean)
-/
@[path]
private lemma main
  {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [IsDomain B] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra.IsIntegral A B]
  {φ : B →ₐ[A] C}
-- given
  (hinj : Function.Injective (algebraMap A C)) :
-- imply
  Function.Injective φ := by
-- proof
  have : Nontrivial A := (algebraMap A C).domain_nontrivial
  rw [injective_iff_map_eq_zero]
  intro b hb
  have hker : RingHom.ker φ.toRingHom = ⊥ := by
    have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
    refine Ideal.eq_bot_of_comap_eq_bot (R := A) ?_
    refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    apply hinj
    rw [map_zero, ← ha]
    exact (φ.commutes a).symm
  have : b ∈ RingHom.ker φ.toRingHom := hb
  rw [hker] at this
  exact this


-- created on 2026-10-05
