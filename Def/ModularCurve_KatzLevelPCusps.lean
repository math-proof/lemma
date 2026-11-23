module

public import Mathlib
public import Theorem.MvPowerSeries.TateSlots
public import Def.ModularCurve_PhiGen
public import Def.ModularCurve_KatzLevelP
public import Abbrev.ModularCurve_KatzLevelPCusps

@[expose] public section

set_option autoImplicit false

noncomputable section

open HahnSeries Polynomial

universe u

namespace ModularCurve

section ToricPoint

variable (R : Type*) [CommRing R] (p : ℕ)

def tateToricPoint (c : Rˣ) : LaurentSeries R × LaurentSeries R :=
  (HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk fun m =>
      if m = 0 then (c : R) * Ring.inverse (1 - (c : R)) ^ 2
      else (∑ d ∈ m.divisors, if p ∣ d then
              ((m / d : ℕ) : R) * ((c : R) ^ (m / d) + ((c⁻¹ : Rˣ) : R) ^ (m / d)) else 0)
        - 2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : R) else 0)),
   HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk fun m =>
      if m = 0 then (c : R) ^ 2 * Ring.inverse (1 - (c : R)) ^ 3
      else (∑ d ∈ m.divisors, if p ∣ d then
              ((m / d).choose 2 : R) * (c : R) ^ (m / d)
                - ((m / d + 1).choose 2 : R) * ((c⁻¹ : Rˣ) : R) ^ (m / d) else 0)
        + (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : R) else 0)))

end ToricPoint

section CuspData

variable (R : Type*) [CommRing R] (p : ℕ)

def cuspPoint (ζ : Rˣ) (v : Fin 2 → ZMod p) : LaurentSeries R × LaurentSeries R :=
  if v 1 = 0 then tateToricPoint R p (ζ ^ (v 0).val)
  else nonToricPoint R p (ζ ^ (v 0).val) (v 1).val

variable {R p} in
variable {R p} in
def cuspData (ζ : Rˣ) (v w : Fin 2 → ZMod p) : LevelPData (LaurentSeries R) where
  xP := (cuspPoint R p ζ v).1
  yP := (cuspPoint R p ζ v).2
  xQ := (cuspPoint R p ζ w).1
  yQ := (cuspPoint R p ζ w).2

def cuspShift (v : Fin 2 → ZMod p) : Fin 2 → ZMod p := ![v 0 + v 1, v 1]

end CuspData

section Twist

variable (R₀ : Type*) [CommRing R₀] {R : Type*} [CommRing R] [Algebra R₀ R]

def qTwistAlgHom (u : Rˣ) : LaurentSeries R →ₐ[R₀] LaurentSeries R :=
  { qTwist u with
    commutes' := fun r => by
      show qTwist u (algebraMap R₀ (LaurentSeries R) r) = algebraMap R₀ (LaurentSeries R) r
      rw [algebraMap_laurentSeries_apply, HahnSeries.C_apply, qTwist_single, zpow_zero, Units.val_one,
        one_mul] }

end Twist

namespace KatzLevelPForm

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} [NeZero p] {k : ℤ}

open Classical in

def evalCusp (F : KatzLevelPForm R₀ p k) (R : Type u) [CommRing R] [Algebra R₀ R] (ζ : Rˣ)
    (v w : Fin 2 → ZMod p) : LaurentSeries R :=
  if h : IsLevelPStructure (tateBase R p) p (cuspData R p ζ v w) then
    F.toFun (tateBase R p) (isUnit_Δ_tateBase R p) (cuspData R p ζ v w) h
  else 0

variable (F : KatzLevelPForm R₀ p k) (R : Type u) [CommRing R] [Algebra R₀ R] (ζ : Rˣ)
  (v w : Fin 2 → ZMod p)

end KatzLevelPForm

section Cycl

variable (R₀ : Type u) [CommRing R₀] (p : ℕ)

variable [NeZero p]

def cyclZeta : (cyclRing R₀ p)ˣ :=
  Units.mkOfMulEqOne (AdjoinRoot.root (Polynomial.cyclotomic p R₀))
    ((AdjoinRoot.root (Polynomial.cyclotomic p R₀)) ^ (p - 1)) (by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne p))]
      exact cyclRing_root_pow R₀ p)

end Cycl

namespace KatzGamma0Form

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} [NeZero p] {k : ℤ}

def qExpansion (φ : KatzGamma0Form R₀ p k) : LaurentSeries (cyclRing R₀ p) :=
  φ.toKatzLevelPForm.evalCusp (cyclRing R₀ p) (cyclZeta R₀ p) ![1, 0] ![0, 1]

end KatzGamma0Form

end ModularCurve

end
