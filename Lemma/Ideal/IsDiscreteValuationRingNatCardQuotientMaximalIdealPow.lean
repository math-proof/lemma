import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (n : ℕ) :
  -- imply
  Nat.card (R ⧸ maximalIdeal R ^ n) = Nat.card (ResidueField R) ^ n := by
  -- proof
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hmax : maximalIdeal R = Ideal.span {π} := hπ.maximalIdeal_eq
  have hpow : ∀ k : ℕ, maximalIdeal R ^ k = Ideal.span {π ^ k} := fun k => by
    rw [hmax, Ideal.span_singleton_pow]
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.one_eq_top]
    let _ : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    apply Nat.card_of_subsingleton (0 : R ⧸ (⊤ : Ideal R))
  | succ n ih =>
    set T : Submodule R R := maximalIdeal R ^ (n + 1) with hT
    set S : Submodule R R := maximalIdeal R ^ n with hS
    have hTS : T ≤ S := Ideal.pow_le_pow_right (Nat.le_succ n)
    have hmul := Submodule.card_quotient_mul_card_quotient S T hTS
    let f : R →ₗ[R] R ⧸ T := LinearMap.comp T.mkQ (LinearMap.lsmul R R (π ^ n))
    have hf : ∀ r, f r = T.mkQ (π ^ n * r) := fun r => rfl
    have hker : LinearMap.ker f = maximalIdeal R := by
      ext r
      rw [LinearMap.mem_ker, hf, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hT, hpow, hmax,
        Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n hπ0)]
    have hrange : LinearMap.range f = Submodule.map T.mkQ S := by
      ext y
      constructor
      ·
        rintro ⟨r, rfl⟩
        refine ⟨π ^ n * r, ?_, rfl⟩
        show π ^ n * r ∈ S
        rw [hS, hpow, Ideal.mem_span_singleton]
        apply dvd_mul_right _ _
      ·
        rintro ⟨x, hx, rfl⟩
        have hx' : x ∈ S := hx
        rw [hS, hpow, Ideal.mem_span_singleton] at hx'
        obtain ⟨r, rfl⟩ := hx'
        refine ⟨r, rfl⟩
    let g : (R ⧸ maximalIdeal R) →ₗ[R] R ⧸ T := (maximalIdeal R).liftQ f hker.ge
    have hginj : Function.Injective g := by
      rw [← LinearMap.ker_eq_bot]
      apply Submodule.ker_liftQ_eq_bot _ _ _ hker.le
    have hgrange : LinearMap.range g = Submodule.map T.mkQ S := by
      rw [Submodule.range_liftQ, hrange]
    have hcardS : Nat.card (Submodule.map T.mkQ S) = Nat.card (ResidueField R) := by
      rw [← hgrange]
      apply (Nat.card_congr (LinearEquiv.ofInjective g hginj).toEquiv).symm
    rw [← hmul, hcardS, ih, pow_succ, mul_comm]


-- created on 2026-10-20
