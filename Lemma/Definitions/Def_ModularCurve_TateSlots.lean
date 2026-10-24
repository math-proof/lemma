import Lemma.Definitions.Def_ModularCurve_TateFormal
import Mathlib.RingTheory.MvPowerSeries.Substitution

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

@[simp] theorem nonToricPoint_fst (K : Type*) [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) :
    (nonToricPoint K p c j).1 = HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivX) := rfl

@[simp] theorem nonToricPoint_snd (K : Type*) [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) :
    (nonToricPoint K p c j).2 = HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivY) := rfl

theorem tateUnivX_apply (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e tateUnivX =
      if e 0 = e 1 then -2 * ∑ d ∈ (e 1).divisors, (d : ℤ)
      else if e 1 < e 0 then (if e 0 - e 1 ∣ e 1 then ((e 0 - e 1 : ℕ) : ℤ) else 0)
      else (if e 1 - e 0 ∣ e 1 then ((e 1 - e 0 : ℕ) : ℤ) else 0) := rfl

theorem tateUnivY_apply (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e tateUnivY =
      if e 0 = e 1 then ∑ d ∈ (e 1).divisors, (d : ℤ)
      else if e 1 < e 0 then (if e 0 - e 1 ∣ e 1 then ((e 0 - e 1).choose 2 : ℤ) else 0)
      else (if e 1 - e 0 ∣ e 1 then -(((e 1 - e 0) + 1).choose 2 : ℤ) else 0) := rfl

theorem tateUnivA4_apply (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e tateUnivA4 =
      if e 0 = e 1 then PowerSeries.coeff (e 0) tateA4 else 0 := rfl

theorem tateUnivA6_apply (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e tateUnivA6 =
      if e 0 = e 1 then PowerSeries.coeff (e 0) tateA6 else 0 := rfl

theorem coeff_tateUnivX (i j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j) tateUnivX =
      if i = j then -2 * ∑ d ∈ j.divisors, (d : ℤ)
      else if j < i then (if i - j ∣ j then ((i - j : ℕ) : ℤ) else 0)
      else (if j - i ∣ j then ((j - i : ℕ) : ℤ) else 0) := by
  rw [tateUnivX_apply]
  simp [Finsupp.add_apply]

theorem coeff_tateUnivY (i j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j) tateUnivY =
      if i = j then ∑ d ∈ j.divisors, (d : ℤ)
      else if j < i then (if i - j ∣ j then ((i - j).choose 2 : ℤ) else 0)
      else (if j - i ∣ j then -(((j - i) + 1).choose 2 : ℤ) else 0) := by
  rw [tateUnivY_apply]
  simp [Finsupp.add_apply]

theorem coeff_tateUnivA4 (i j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j) tateUnivA4 =
      if i = j then PowerSeries.coeff i tateA4 else 0 := by
  rw [tateUnivA4_apply]
  simp [Finsupp.add_apply]

theorem coeff_tateUnivA6 (i j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j) tateUnivA6 =
      if i = j then PowerSeries.coeff i tateA6 else 0 := by
  rw [tateUnivA6_apply]
  simp [Finsupp.add_apply]

@[simp] theorem tateUnivCurve_a₁ : tateUnivCurve.a₁ = 1 := rfl

@[simp] theorem tateUnivCurve_a₂ : tateUnivCurve.a₂ = 0 := rfl

@[simp] theorem tateUnivCurve_a₃ : tateUnivCurve.a₃ = 0 := rfl

@[simp] theorem tateUnivCurve_a₄ : tateUnivCurve.a₄ = tateUnivA4 := rfl

@[simp] theorem tateUnivCurve_a₆ : tateUnivCurve.a₆ = tateUnivA6 := rfl

open scoped Classical in

theorem mem_nonToricSlotSet (K : Type*) [CommRing K] (p : ℕ) (ζ : Kˣ) (b : ℕ)
    (P : LaurentSeries K × LaurentSeries K) :
    P ∈ nonToricSlotSet K p ζ b ↔
      ∃ k ∈ Finset.Icc 1 (p / 2), nonToricPoint K p (ζ ^ (b * k)) k = P := by
  rw [nonToricSlotSet]; exact Finset.mem_image

instance instIsElliptic_tateBase (K : Type*) [CommRing K] (p : ℕ) [NeZero p] :
    (tateBase K p).IsElliptic := by
  unfold tateBase; infer_instance

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

@[simp] theorem toricPoint_fst (K : Type*) [Field K] (p : ℕ) (c : K) :
    (toricPoint K p c).1 = HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun m =>
      if m = 0 then c / (1 - c) ^ 2
      else (∑ d ∈ m.divisors, if p ∣ d then ((m / d : ℕ) : K) * (c ^ (m / d) + c⁻¹ ^ (m / d)) else 0)
        - 2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : K) else 0)) := rfl

@[simp] theorem toricPoint_snd (K : Type*) [Field K] (p : ℕ) (c : K) :
    (toricPoint K p c).2 = HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun m =>
      if m = 0 then c ^ 2 / (1 - c) ^ 3
      else (∑ d ∈ m.divisors, if p ∣ d then
              ((m / d).choose 2 : K) * c ^ (m / d) - ((m / d + 1).choose 2 : K) * c⁻¹ ^ (m / d) else 0)
        + (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : K) else 0)) := rfl

open scoped Classical in

def toricSlotSet (K : Type*) [Field K] (p : ℕ) (ζ : Kˣ) :
    Finset (LaurentSeries K × LaurentSeries K) :=
  (Finset.Icc 1 (p / 2)).image fun k => toricPoint K p ((ζ : K) ^ k)

def veluSlotSet (K : Type*) [Field K] (p : ℕ) (ζ : Kˣ) (i : Fin (p + 1)) :
    Finset (LaurentSeries K × LaurentSeries K) :=
  if (i : ℕ) = 0 then toricSlotSet K p ζ else nonToricSlotSet K p ζ ((i : ℕ) - 1)

theorem veluSlotSet_zero (K : Type*) [Field K] (p : ℕ) (ζ : Kˣ) :
    veluSlotSet K p ζ 0 = toricSlotSet K p ζ := by
  simp [veluSlotSet]

theorem veluSlotSet_succ (K : Type*) [Field K] (p : ℕ) (ζ : Kˣ) (b : Fin p) :
    veluSlotSet K p ζ b.succ = nonToricSlotSet K p ζ (b : ℕ) := by
  simp [veluSlotSet]

open scoped Classical in

theorem mem_toricSlotSet (K : Type*) [Field K] (p : ℕ) (ζ : Kˣ)
    (P : LaurentSeries K × LaurentSeries K) :
    P ∈ toricSlotSet K p ζ ↔
      ∃ k ∈ Finset.Icc 1 (p / 2), toricPoint K p ((ζ : K) ^ k) = P := by
  rw [toricSlotSet]; exact Finset.mem_image

theorem mem_veluSlotSet_zero (K : Type*) [Field K] (p : ℕ) (ζ : Kˣ)
    (P : LaurentSeries K × LaurentSeries K) :
    P ∈ veluSlotSet K p ζ 0 ↔
      ∃ k ∈ Finset.Icc 1 (p / 2), toricPoint K p ((ζ : K) ^ k) = P := by
  rw [veluSlotSet_zero]; exact mem_toricSlotSet K p ζ P

theorem mem_veluSlotSet_succ (K : Type*) [Field K] (p : ℕ) (ζ : Kˣ) (b : Fin p)
    (P : LaurentSeries K × LaurentSeries K) :
    P ∈ veluSlotSet K p ζ b.succ ↔
      ∃ k ∈ Finset.Icc 1 (p / 2), nonToricPoint K p (ζ ^ ((b : ℕ) * k)) k = P := by
  rw [veluSlotSet_succ]; exact mem_nonToricSlotSet K p ζ (b : ℕ) P

end ModularCurve

end
