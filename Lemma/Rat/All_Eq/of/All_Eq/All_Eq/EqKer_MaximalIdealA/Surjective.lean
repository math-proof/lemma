import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalRing_residueMap_comp_algHom_eq_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_residueMap_comp_algHom_eq_of_surjective.lean)
-/
@[path]
private lemma main
  [CommRing Λ] [Field k] [CommRing A] [IsLocalRing A] [Algebra Λ A] [CommRing B] [Algebra Λ B]
  {res₀ : Λ →+* k}
  {rA : A →+* k}
  {rB : B →+* k}
  {Φ : A →ₐ[Λ] B}
-- given
  (hres₀ : Function.Surjective res₀)
  (hkerA : RingHom.ker rA = maximalIdeal A)
  (hrA : ∀ w : Λ, rA (algebraMap Λ A w) = res₀ w)
  (hrB : ∀ w : Λ, rB (algebraMap Λ B w) = res₀ w) :
-- imply
  ∀ a : A, rB (Φ a) = rA a := by
-- proof
  intro a
  let r' : A →+* k := rB.comp Φ.toRingHom
  have hr'w : ∀ w, r' (algebraMap Λ A w) = res₀ w := fun w => by
    show rB (Φ (algebraMap Λ A w)) = res₀ w
    rw [Φ.commutes, hrB]
  have hsurj : Function.Surjective r' := fun x => by
    obtain ⟨w, hw⟩ := hres₀ x
    exact ⟨algebraMap Λ A w, (hr'w w).trans hw⟩
  have hker' : RingHom.ker r' = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r' hsurj)
  obtain ⟨w, hw⟩ := hres₀ (rA a)
  have hm : a - algebraMap Λ A w ∈ maximalIdeal A := by
    rw [← hkerA, RingHom.mem_ker, map_sub, hrA, hw, sub_self]
  have hm' : a - algebraMap Λ A w ∈ RingHom.ker r' := by rw [hker']; exact hm
  rw [RingHom.mem_ker, map_sub, hr'w, sub_eq_zero] at hm'
  show r' a = rA a
  rw [hm', hw]


-- created on 2026-10-05
