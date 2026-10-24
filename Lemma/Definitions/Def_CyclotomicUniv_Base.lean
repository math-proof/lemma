import Mathlib

set_option autoImplicit false

noncomputable section

open Polynomial

namespace CyclotomicUniv

variable (N : ℕ)

abbrev R₀ : Type := AdjoinRoot (cyclotomic N ℤ)

abbrev ζ₀ : R₀ N := AdjoinRoot.root (cyclotomic N ℤ)

def den : R₀ N := (N : R₀ N) * ∏ k ∈ Finset.Ico 1 N, (1 - ζ₀ N ^ k)

abbrev base : Type := Localization.Away (den N)

def ζ : base N := algebraMap (R₀ N) (base N) (ζ₀ N)

theorem algebraMap_ζ₀ : algebraMap (R₀ N) (base N) (ζ₀ N) = ζ N := rfl

theorem algebraMap_den :
    algebraMap (R₀ N) (base N) (den N) = (N : base N) * ∏ k ∈ Finset.Ico 1 N, (1 - ζ N ^ k) := by
  simp only [den, map_mul, map_natCast, map_prod, map_sub, map_one, map_pow, algebraMap_ζ₀]

section Basic

variable [NeZero N]

theorem degree_cyclotomic_ne_zero : (cyclotomic N ℤ).degree ≠ 0 := by
  rw [degree_cyclotomic]
  exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos N)).ne'

instance instIsDomainR₀ : IsDomain (R₀ N) :=
  AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible (NeZero.pos N)).prime

theorem of_injective : Function.Injective (AdjoinRoot.of (cyclotomic N ℤ)) :=
  AdjoinRoot.of.injective_of_degree_ne_zero (degree_cyclotomic_ne_zero N)

instance instCharZeroR₀ : CharZero (R₀ N) where
  cast_injective a b h := by
    have h' : AdjoinRoot.of (cyclotomic N ℤ) (a : ℤ) = AdjoinRoot.of (cyclotomic N ℤ) (b : ℤ) := by
      rwa [map_natCast, map_natCast]
    exact_mod_cast of_injective N h'

theorem isPrimitiveRoot_ζ₀ : IsPrimitiveRoot (ζ₀ N) N := by
  have h := AdjoinRoot.isRoot_root (cyclotomic N ℤ)
  rw [map_cyclotomic] at h
  exact (isRoot_cyclotomic_iff (R := R₀ N)).mp h

theorem den_ne_zero : den N ≠ 0 := by
  rw [den]
  refine mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact sub_ne_zero.mpr (Ne.symm ((isPrimitiveRoot_ζ₀ N).pow_ne_one_of_pos_of_lt (by omega) hk.2))

theorem powers_den_le : Submonoid.powers (den N) ≤ nonZeroDivisors (R₀ N) :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (den_ne_zero N)

instance instIsDomain : IsDomain (base N) :=
  IsLocalization.isDomain_localization (powers_den_le N)

theorem algebraMap_injective : Function.Injective (algebraMap (R₀ N) (base N)) :=
  IsLocalization.injective (base N) (powers_den_le N)

instance instCharZero : CharZero (base N) where
  cast_injective a b h := by
    have h' : algebraMap (R₀ N) (base N) (a : R₀ N) = algebraMap (R₀ N) (base N) (b : R₀ N) := by
      rwa [map_natCast, map_natCast]
    exact_mod_cast algebraMap_injective N h'

theorem isPrimitiveRoot_ζ : IsPrimitiveRoot (ζ N) N :=
  (isPrimitiveRoot_ζ₀ N).map_of_injective (algebraMap_injective N)

omit [NeZero N] in
theorem isUnit_den : IsUnit (algebraMap (R₀ N) (base N) (den N)) :=
  IsLocalization.Away.algebraMap_isUnit (den N)

omit [NeZero N] in

theorem isUnit_natCast : IsUnit (N : base N) :=
  isUnit_of_dvd_unit (Dvd.intro _ (algebraMap_den N).symm) (isUnit_den N)

omit [NeZero N] in

theorem isUnit_natCast_of_dvd {ℓ : ℕ} (h : ℓ ∣ N) : IsUnit (ℓ : base N) :=
  isUnit_of_dvd_unit (Nat.cast_dvd_cast h) (isUnit_natCast N)

omit [NeZero N] in

theorem isUnit_one_sub_ζ_pow {k : ℕ} (hk : 0 < k) (hkN : k < N) : IsUnit (1 - ζ N ^ k) := by
  have hu : IsUnit ((N : base N) * ∏ k ∈ Finset.Ico 1 N, (1 - ζ N ^ k)) := by
    rw [← algebraMap_den]; exact isUnit_den N
  exact isUnit_of_dvd_unit
    (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun k => 1 - ζ N ^ k) (Finset.mem_Ico.mpr ⟨hk, hkN⟩)) _) hu

def ζUnit : (base N)ˣ := ((isPrimitiveRoot_ζ N).isUnit (NeZero.ne N)).unit

@[simp] theorem val_ζUnit : (ζUnit N : base N) = ζ N := rfl

omit [NeZero N] in

def invNat (ℓ : ℕ) (h : ℓ ∣ N) : base N := ((isUnit_natCast_of_dvd N h).unit⁻¹ : (base N)ˣ)

omit [NeZero N] in
theorem natCast_mul_invNat (ℓ : ℕ) (h : ℓ ∣ N) : (ℓ : base N) * invNat N ℓ h = 1 := by
  rw [invNat]
  exact (isUnit_natCast_of_dvd N h).mul_val_inv

omit [NeZero N] in
theorem invNat_mul_natCast (ℓ : ℕ) (h : ℓ ∣ N) : invNat N ℓ h * (ℓ : base N) = 1 := by
  rw [mul_comm, natCast_mul_invNat]

end Basic

section Lift

variable {N} [NeZero N] {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z N)
include hz

theorem eval₂_cyclotomic_eq_zero : (cyclotomic N ℤ).eval₂ (Int.castRingHom F) z = 0 := by
  rw [eval₂_eq_eval_map, map_cyclotomic_int]
  exact hz.isRoot_cyclotomic (NeZero.pos N)

def lift₀ : R₀ N →+* F := AdjoinRoot.lift (Int.castRingHom F) z (eval₂_cyclotomic_eq_zero hz)

@[simp] theorem lift₀_ζ₀ : lift₀ hz (ζ₀ N) = z := AdjoinRoot.lift_root _

theorem lift₀_den : lift₀ hz (den N) = (N : F) * ∏ k ∈ Finset.Ico 1 N, (1 - z ^ k) := by
  simp only [den, map_mul, map_natCast, map_prod, map_sub, map_one, map_pow, lift₀_ζ₀]

theorem isUnit_lift₀_den : IsUnit (lift₀ hz (den N)) := by
  rw [lift₀_den, isUnit_iff_ne_zero]
  haveI : NeZero ((N : ℕ) : F) := hz.neZero'
  refine mul_ne_zero (NeZero.ne (N : F)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact sub_ne_zero.mpr (Ne.symm (hz.pow_ne_one_of_pos_of_lt (by omega) hk.2))

def lift : base N →+* F := IsLocalization.Away.lift (den N) (isUnit_lift₀_den hz)

@[simp] theorem lift_algebraMap (x : R₀ N) : lift hz (algebraMap (R₀ N) (base N) x) = lift₀ hz x :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem lift_ζ : lift hz (ζ N) = z := by
  rw [← algebraMap_ζ₀, lift_algebraMap, lift₀_ζ₀]

theorem lift_ζUnit : lift hz (ζUnit N) = z := by
  rw [val_ζUnit, lift_ζ]

theorem lift_invNat (ℓ : ℕ) (h : ℓ ∣ N) : lift hz (invNat N ℓ h) = (ℓ : F)⁻¹ := by
  have h1 : (ℓ : F) * lift hz (invNat N ℓ h) = 1 := by
    have := congrArg (lift hz) (natCast_mul_invNat N ℓ h)
    rwa [map_mul, map_natCast, map_one] at this
  have hℓ : (ℓ : F) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact zero_ne_one h1
  exact (eq_inv_of_mul_eq_one_right h1)

theorem lift₀_injective [CharZero F] : Function.Injective (lift₀ hz) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih P =>
    rw [lift₀, AdjoinRoot.lift_mk] at hx
    rw [AdjoinRoot.mk_eq_zero, cyclotomic_eq_minpoly hz (NeZero.pos N)]
    refine minpoly.isIntegrallyClosed_dvd (hz.isIntegral (NeZero.pos N)) ?_
    rwa [aeval_def, show algebraMap ℤ F = Int.castRingHom F from RingHom.ext_int _ _]

theorem lift_injective [CharZero F] : Function.Injective (lift hz) := by
  rw [lift, IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h; rw [algebraMap_injective N h]
  · intro h; rw [lift₀_injective hz h]

end Lift

end CyclotomicUniv

end
