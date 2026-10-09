import Mathlib
import sympy.Basic

open Polynomial

/--
[AddMonoidAlgebra_ringKrullDim_pi_fin_int_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidAlgebra_ringKrullDim_pi_fin_int_eq.lean)
-/

private lemma  ringKrullDim_le_of_isLocalization {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (fun p : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) p)
  refine Monotone.strictMono_of_injective (fun p q h => ?_) (PrimeSpectrum.localization_comap_injective S M)
  exact Ideal.comap_mono h

private lemma  ringKrullDim_laurentPolynomial (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] :
  ringKrullDim (LaurentPolynomial R) = ringKrullDim R + 1 := by
  apply le_antisymm
  ·
    calc _ ≤ ringKrullDim R[X] :=
          ringKrullDim_le_of_isLocalization (.powers (X : R[X])) (LaurentPolynomial R)
      _ = ringKrullDim R + 1 := Polynomial.ringKrullDim_of_isNoetherianRing
  ·
    let φ : LaurentPolynomial R →ₐ[R] R := AddMonoidAlgebra.lift R R ℤ 1
    have hφT : φ (LaurentPolynomial.T 1) = 1 := by
      show AddMonoidAlgebra.lift R R ℤ 1 (AddMonoidAlgebra.single 1 1) = 1
      rw [AddMonoidAlgebra.lift_single]; simp
    have hsurj : Function.Surjective φ := fun r => ⟨algebraMap R _ r, φ.commutes r⟩
    have hne : (LaurentPolynomial.T 1 - 1 : LaurentPolynomial R) ≠ 0 := by
      refine sub_ne_zero.mpr (fun h => ?_)
      have hd := congrArg LaurentPolynomial.degree h
      rw [LaurentPolynomial.degree_T, ← LaurentPolynomial.T_zero, LaurentPolynomial.degree_T] at hd
      exact one_ne_zero (WithBot.coe_injective hd)
    have hr : (LaurentPolynomial.T 1 - 1 : LaurentPolynomial R) ∈ nonZeroDivisors (LaurentPolynomial R) :=
      mem_nonZeroDivisors_of_ne_zero hne
    have := ringKrullDim_succ_le_of_surjective φ.toRingHom hsurj hr (by simp [hφT])
    exact this

private lemma  noeth_and_dim (κ : Type*) [Field κ] :
  ∀ t : ℕ, IsNoetherianRing (AddMonoidAlgebra κ (Fin t → ℤ)) ∧ ringKrullDim (AddMonoidAlgebra κ (Fin t → ℤ)) = t
  | 0 => by
      let e : AddMonoidAlgebra κ (Fin 0 → ℤ) ≃+* κ := AddMonoidAlgebra.uniqueRingEquiv (Fin 0 → ℤ)
      refine ⟨isNoetherianRing_of_ringEquiv κ e.symm, ?_⟩
      rw [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_zero_of_field]
      rfl
  | (t + 1) => by
      obtain ⟨hN, hd⟩ := noeth_and_dim κ t
      let e1 : (Fin (t + 1) → ℤ) ≃+ ℤ × (Fin t → ℤ) :=
        { (Fin.consEquiv fun _ : Fin (t + 1) => ℤ).symm with
          map_add' := fun f g => rfl }
      let E : AddMonoidAlgebra κ (Fin (t + 1) → ℤ) ≃+* LaurentPolynomial (AddMonoidAlgebra κ (Fin t → ℤ)) :=
        (AddMonoidAlgebra.domCongr κ κ e1).toRingEquiv.trans AddMonoidAlgebra.curryRingEquiv
      have := hN
      have : IsNoetherianRing (LaurentPolynomial (AddMonoidAlgebra κ (Fin t → ℤ))) :=
        IsLocalization.isNoetherianRing (.powers (X : (AddMonoidAlgebra κ (Fin t → ℤ))[X])) _ inferInstance
      refine ⟨isNoetherianRing_of_ringEquiv _ E.symm, ?_⟩
      rw [ringKrullDim_eq_of_ringEquiv E, ringKrullDim_laurentPolynomial, hd]
      rfl
@[main]
private lemma main
  [Field κ]
  {t : ℕ} :
-- imply
  ringKrullDim (AddMonoidAlgebra κ (Fin t → ℤ)) = t :=
-- proof
  (noeth_and_dim κ t).2


-- created on 2026-10-09
