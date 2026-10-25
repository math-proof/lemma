import Mathlib
import sympy.Basic
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Lemma.Int.P2MUtil
open scoped TensorProduct


private lemma charZero_zp2 (p : ℕ) [Fact p.Prime] : CharZero (CerednikDrinfeld.Zp2 p) := by
  have : Fact p.Prime := inferInstance
  rw [CharZero.charZero_iff_forall_prime_ne_zero]
  intro ℓ hℓ hzero
  if hℓp : ℓ = p then
    subst hℓp
    exact WittVector.p_nonzero _ _ hzero
  else
    have h0 : (WittVector.constantCoeff : WittVector p (GaloisField p 2) →+* GaloisField p 2) (ℓ : WittVector p (GaloisField p 2)) = 0 := by
      rw [hzero, map_zero]
    rw [map_natCast, CharP.cast_eq_zero_iff (GaloisField p 2) p ℓ] at h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h0).symm

/--
[CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_and_comp_eq_of_surjective.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {S B : Type} [CommRing S] [CommRing B]
  {φ : S →+* B}
  {j : CerednikDrinfeld.Zp2 p →+* B}
-- given
  (hφ : Function.Surjective φ)
  (hS : ∀ s : S, (p : S) * s = 0 → s = 0) :
-- imply
  ∃ (S' : Type) (_ : CommRing S') (ι : S →+* S') (j' : CerednikDrinfeld.Zp2 p →+* S') (q : S' →+* B),
      (∀ s : S', (p : S') * s = 0 → s = 0) ∧ Function.Surjective q ∧ q.comp ι = φ ∧ q.comp j' = j := by
-- proof
  classical
  have : CharZero (CerednikDrinfeld.Zp2 p) := charZero_zp2 p
  let W : Type := CerednikDrinfeld.Zp2 p
  let S' : Type := S ⊗[ℤ] W
  let ι : S →+* S' := Algebra.TensorProduct.includeLeftRingHom
  let j' : W →+* S' := (Algebra.TensorProduct.includeRight : W →ₐ[ℤ] S ⊗[ℤ] W).toRingHom
  let q : S' →+* B :=
    (Algebra.TensorProduct.lift φ.toIntAlgHom j.toIntAlgHom (fun x y => Commute.all _ _)).toRingHom
  have hq_tmul : ∀ (s : S) (w : W), q (s ⊗ₜ[ℤ] w) = φ s * j w := fun s w =>
    Algebra.TensorProduct.lift_tmul _ _ _ s w
  refine ⟨S', inferInstance, ι, j', q, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    let f : S →ₗ[ℤ] S := LinearMap.mulLeft ℤ (p : S)
    have hinj : Function.Injective f := by
      intro a b hab
      apply sub_eq_zero.mp
      apply hS
      have : (p : S) * a = (p : S) * b := by simpa [f] using hab
      rw [mul_sub, this, sub_self]
    have hT := Module.Flat.rTensor_preserves_injective_linearMap (M := W) f hinj
    have key : ∀ y : S', f.rTensor W y = ((p : S) ⊗ₜ[ℤ] (1 : W)) * y := by
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul s w =>
          rw [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | add a b ha hb => rw [map_add, ha, hb, mul_add]
    have hp : ((p : S) ⊗ₜ[ℤ] (1 : W) : S') = (p : S') := by
      rw [← map_natCast ι p]; rfl
    apply hT
    rwa [key, key, mul_zero, hp]
  ·
    intro b
    obtain ⟨s, rfl⟩ := hφ b
    refine ⟨ι s, ?_⟩
    show q (s ⊗ₜ[ℤ] (1 : W)) = φ s
    rw [hq_tmul, map_one, mul_one]
  ·
    refine RingHom.ext fun s => ?_
    show q (s ⊗ₜ[ℤ] (1 : W)) = φ s
    rw [hq_tmul, map_one, mul_one]
  ·
    refine RingHom.ext fun w => ?_
    show q ((1 : S) ⊗ₜ[ℤ] w) = j w
    rw [hq_tmul, map_one, one_mul]


-- created on 2026-10-24
