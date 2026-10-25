import Instance.ModularCurve_TateFormal
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Instance.ModularCurve_TateSlots

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def tateUnivX : MvPowerSeries (Fin 2) ℤ := fun e =>
  if e 0 = e 1 then -2 * ∑ d ∈ (e 1).divisors, (d : ℤ)
  else if e 1 < e 0 then (if e 0 - e 1 ∣ e 1 then ((e 0 - e 1 : ℕ) : ℤ) else 0)
  else (if e 1 - e 0 ∣ e 1 then ((e 1 - e 0 : ℕ) : ℤ) else 0)

def tateUnivY : MvPowerSeries (Fin 2) ℤ := fun e =>
  if e 0 = e 1 then ∑ d ∈ (e 1).divisors, (d : ℤ)
  else if e 1 < e 0 then (if e 0 - e 1 ∣ e 1 then ((e 0 - e 1).choose 2 : ℤ) else 0)
  else (if e 1 - e 0 ∣ e 1 then -(((e 1 - e 0) + 1).choose 2 : ℤ) else 0)

def tateUnivA4 : MvPowerSeries (Fin 2) ℤ := fun e =>
  if e 0 = e 1 then PowerSeries.coeff (e 0) tateA4 else 0

def tateUnivA6 : MvPowerSeries (Fin 2) ℤ := fun e =>
  if e 0 = e 1 then PowerSeries.coeff (e 0) tateA6 else 0

def tateUnivCurve : WeierstrassCurve (MvPowerSeries (Fin 2) ℤ) := ⟨1, 0, 0, tateUnivA4, tateUnivA6⟩

def slotFamily (K : Type*) [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) : Fin 2 → PowerSeries K :=
  ![PowerSeries.C (c : K) * PowerSeries.X ^ j, PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)]

def slotSubst (K : Type*) [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (f : MvPowerSeries (Fin 2) ℤ) :
    PowerSeries K :=
  MvPowerSeries.subst (slotFamily K p c j) f

def nonToricPoint (K : Type*) [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) :
    LaurentSeries K × LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivX),
   HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivY))

open scoped Classical in

def nonToricSlotSet (K : Type*) [CommRing K] (p : ℕ) (ζ : Kˣ) (b : ℕ) :
    Finset (LaurentSeries K × LaurentSeries K) :=
  (Finset.Icc 1 (p / 2)).image fun k => nonToricPoint K p (ζ ^ (b * k)) k

def tateBase (K : Type*) [CommRing K] (p : ℕ) [NeZero p] : WeierstrassCurve (LaurentSeries K) :=
  (tateLaurent K).map (qExpand K p)


def toricPoint (K : Type*) [Field K] (p : ℕ) (c : K) :
    LaurentSeries K × LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun m =>
      if m = 0 then c / (1 - c) ^ 2
      else (∑ d ∈ m.divisors, if p ∣ d then ((m / d : ℕ) : K) * (c ^ (m / d) + c⁻¹ ^ (m / d)) else 0)
        - 2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : K) else 0)),
   HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun m =>
      if m = 0 then c ^ 2 / (1 - c) ^ 3
      else (∑ d ∈ m.divisors, if p ∣ d then
              ((m / d).choose 2 : K) * c ^ (m / d) - ((m / d + 1).choose 2 : K) * c⁻¹ ^ (m / d) else 0)
        + (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : K) else 0)))


open scoped Classical in

def toricSlotSet (K : Type*) [Field K] (p : ℕ) (ζ : Kˣ) :
    Finset (LaurentSeries K × LaurentSeries K) :=
  (Finset.Icc 1 (p / 2)).image fun k => toricPoint K p ((ζ : K) ^ k)

def veluSlotSet (K : Type*) [Field K] (p : ℕ) (ζ : Kˣ) (i : Fin (p + 1)) :
    Finset (LaurentSeries K × LaurentSeries K) :=
  if (i : ℕ) = 0 then toricSlotSet K p ζ else nonToricSlotSet K p ζ ((i : ℕ) - 1)

end ModularCurve

end
