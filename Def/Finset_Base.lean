module
public import Mathlib
public import Instance.CyclotomicUniv_Base
public import Abbrev.CyclotomicUniv_Base
set_option autoImplicit false


public section

noncomputable section

open Polynomial

namespace CyclotomicUniv

variable (N : ℕ)

abbrev ζ₀ : R₀ N := AdjoinRoot.root (cyclotomic N ℤ)

def den : R₀ N := (N : R₀ N) * ∏ k ∈ Finset.Ico 1 N, (1 - ζ₀ N ^ k)

abbrev base : Type := Localization.Away (den N)

def ζ : base N := algebraMap (R₀ N) (base N) (ζ₀ N)

section Basic

variable [NeZero N]

def ζUnit : (base N)ˣ := ((isPrimitiveRoot_ζ N).isUnit (NeZero.ne N)).unit

def invNat (ℓ : ℕ) (h : ℓ ∣ N) : base N := ((isUnit_natCast_of_dvd N h).unit⁻¹ : (base N)ˣ)

omit [NeZero N] in
end Basic

section Lift

variable {N} [NeZero N] {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z N)
include hz

def lift₀ : R₀ N →+* F := AdjoinRoot.lift (Int.castRingHom F) z (eval₂_cyclotomic_eq_zero hz)

def lift : base N →+* F := IsLocalization.Away.lift (den N) (isUnit_lift₀_den hz)

end Lift

end CyclotomicUniv

end
