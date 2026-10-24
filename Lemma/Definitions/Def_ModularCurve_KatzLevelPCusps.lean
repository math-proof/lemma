import Mathlib
import Lemma.Definitions.Def_ModularCurve_TateSlots
import Lemma.Definitions.Def_ModularCurve_PhiGen
import Lemma.Definitions.Def_ModularCurve_KatzLevelP

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

theorem tateToricPoint_fst (c : Rˣ) : (tateToricPoint R p c).1 =
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk fun m =>
      if m = 0 then (c : R) * Ring.inverse (1 - (c : R)) ^ 2
      else (∑ d ∈ m.divisors, if p ∣ d then
              ((m / d : ℕ) : R) * ((c : R) ^ (m / d) + ((c⁻¹ : Rˣ) : R) ^ (m / d)) else 0)
        - 2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : R) else 0)) := rfl

theorem tateToricPoint_snd (c : Rˣ) : (tateToricPoint R p c).2 =
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk fun m =>
      if m = 0 then (c : R) ^ 2 * Ring.inverse (1 - (c : R)) ^ 3
      else (∑ d ∈ m.divisors, if p ∣ d then
              ((m / d).choose 2 : R) * (c : R) ^ (m / d)
                - ((m / d + 1).choose 2 : R) * ((c⁻¹ : Rˣ) : R) ^ (m / d) else 0)
        + (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : R) else 0)) := rfl

theorem tateToricPoint_eq_toricPoint (K : Type*) [Field K] (p : ℕ) (c : Kˣ) :
    tateToricPoint K p c = toricPoint K p (c : K) := by
  have hinv : ((c⁻¹ : Kˣ) : K) = (c : K)⁻¹ := Units.val_inv_eq_inv_val c
  simp only [tateToricPoint, toricPoint, Ring.inverse_eq_inv', hinv, div_eq_mul_inv, inv_pow]

end ToricPoint

section CuspData

variable (R : Type*) [CommRing R] (p : ℕ)

def cuspPoint (ζ : Rˣ) (v : Fin 2 → ZMod p) : LaurentSeries R × LaurentSeries R :=
  if v 1 = 0 then tateToricPoint R p (ζ ^ (v 0).val)
  else nonToricPoint R p (ζ ^ (v 0).val) (v 1).val

variable {R p} in
theorem cuspPoint_of_eq_zero (ζ : Rˣ) {v : Fin 2 → ZMod p} (hv : v 1 = 0) :
    cuspPoint R p ζ v = tateToricPoint R p (ζ ^ (v 0).val) := if_pos hv

variable {R p} in
theorem cuspPoint_of_ne_zero (ζ : Rˣ) {v : Fin 2 → ZMod p} (hv : v 1 ≠ 0) :
    cuspPoint R p ζ v = nonToricPoint R p (ζ ^ (v 0).val) (v 1).val := if_neg hv

def cuspData (ζ : Rˣ) (v w : Fin 2 → ZMod p) : LevelPData (LaurentSeries R) where
  xP := (cuspPoint R p ζ v).1
  yP := (cuspPoint R p ζ v).2
  xQ := (cuspPoint R p ζ w).1
  yQ := (cuspPoint R p ζ w).2

@[simp] theorem cuspData_xP (ζ : Rˣ) (v w : Fin 2 → ZMod p) :
    (cuspData R p ζ v w).xP = (cuspPoint R p ζ v).1 := rfl
@[simp] theorem cuspData_yP (ζ : Rˣ) (v w : Fin 2 → ZMod p) :
    (cuspData R p ζ v w).yP = (cuspPoint R p ζ v).2 := rfl
@[simp] theorem cuspData_xQ (ζ : Rˣ) (v w : Fin 2 → ZMod p) :
    (cuspData R p ζ v w).xQ = (cuspPoint R p ζ w).1 := rfl
@[simp] theorem cuspData_yQ (ζ : Rˣ) (v w : Fin 2 → ZMod p) :
    (cuspData R p ζ v w).yQ = (cuspPoint R p ζ w).2 := rfl

theorem cuspData_swap (ζ : Rˣ) (v w : Fin 2 → ZMod p) :
    (cuspData R p ζ v w).swap = cuspData R p ζ w v := rfl

def cuspShift (v : Fin 2 → ZMod p) : Fin 2 → ZMod p := ![v 0 + v 1, v 1]

@[simp] theorem cuspShift_zero (v : Fin 2 → ZMod p) : cuspShift p v 0 = v 0 + v 1 := rfl
@[simp] theorem cuspShift_one (v : Fin 2 → ZMod p) : cuspShift p v 1 = v 1 := rfl

end CuspData

section Twist

variable (R₀ : Type*) [CommRing R₀] {R : Type*} [CommRing R] [Algebra R₀ R]

theorem algebraMap_laurentSeries_apply (r : R₀) :
    algebraMap R₀ (LaurentSeries R) r = HahnSeries.C (algebraMap R₀ R r) := by
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap R₀ (PowerSeries R) r = PowerSeries.C (algebraMap R₀ R r) := by
    simp [PowerSeries.algebraMap_apply]
  rw [h1, HahnSeries.ofPowerSeries_C]

def qTwistAlgHom (u : Rˣ) : LaurentSeries R →ₐ[R₀] LaurentSeries R :=
  { qTwist u with
    commutes' := fun r => by
      show qTwist u (algebraMap R₀ (LaurentSeries R) r) = algebraMap R₀ (LaurentSeries R) r
      rw [algebraMap_laurentSeries_apply, HahnSeries.C_apply, qTwist_single, zpow_zero, Units.val_one,
        one_mul] }

@[simp] theorem qTwistAlgHom_apply (u : Rˣ) (f : LaurentSeries R) :
    qTwistAlgHom R₀ u f = qTwist u f := rfl

theorem coe_qTwistAlgHom (u : Rˣ) :
    ((qTwistAlgHom R₀ u : LaurentSeries R →ₐ[R₀] LaurentSeries R) : LaurentSeries R →+* LaurentSeries R)
      = qTwist u :=
  RingHom.ext fun _ => rfl

theorem qTwist_qExpand_of_pow_eq_one (p : ℕ) [NeZero p] (ζ : Rˣ) (hζ : ζ ^ p = 1)
    (f : LaurentSeries R) : qTwist ζ (qExpand R p f) = qExpand R p f := by
  rw [qTwist_qExpand, zpow_natCast, hζ, qTwist_one_apply]

theorem tateBase_map_qTwist (p : ℕ) [NeZero p] (ζ : Rˣ) (hζ : ζ ^ p = 1) :
    (tateBase R p).map (qTwist ζ) = tateBase R p := by
  simp only [tateBase, tateLaurent, WeierstrassCurve.map, qTwist_qExpand_of_pow_eq_one p ζ hζ]

end Twist

theorem isUnit_Δ_tateBase (R : Type*) [CommRing R] (p : ℕ) [NeZero p] : IsUnit (tateBase R p).Δ :=
  (tateBase R p).isUnit_Δ

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

theorem evalCusp_eq (h : IsLevelPStructure (tateBase R p) p (cuspData R p ζ v w)) :
    F.evalCusp R ζ v w = F.toFun (tateBase R p) (isUnit_Δ_tateBase R p) (cuspData R p ζ v w) h :=
  dif_pos h

theorem evalCusp_of_not (h : ¬ IsLevelPStructure (tateBase R p) p (cuspData R p ζ v w)) :
    F.evalCusp R ζ v w = 0 :=
  dif_neg h

theorem evalCusp_eq_zero_iff :
    F.evalCusp R ζ v w = 0 ↔ ∀ h : IsLevelPStructure (tateBase R p) p (cuspData R p ζ v w),
      F.toFun (tateBase R p) (isUnit_Δ_tateBase R p) (cuspData R p ζ v w) h = 0 := by
  constructor
  · intro h0 h; rwa [evalCusp_eq F R ζ v w h] at h0
  · intro H
    by_cases h : IsLevelPStructure (tateBase R p) p (cuspData R p ζ v w)
    · rw [evalCusp_eq F R ζ v w h]; exact H h
    · exact evalCusp_of_not F R ζ v w h

theorem evalCusp_eq_iff (f : LaurentSeries R)
    (h : IsLevelPStructure (tateBase R p) p (cuspData R p ζ v w)) :
    F.evalCusp R ζ v w = f ↔
      F.toFun (tateBase R p) (isUnit_Δ_tateBase R p) (cuspData R p ζ v w) h = f := by
  rw [evalCusp_eq F R ζ v w h]

end KatzLevelPForm

theorem evalCusp_pullbackLevelP {R₀ : Type u} [CommRing R₀] {p : ℕ} [NeZero p] {k : ℤ}
    (g : KatzModularForm R₀ k) (R : Type u) [CommRing R] [Algebra R₀ R] (ζ : Rˣ)
    (v w : Fin 2 → ZMod p) (h : IsLevelPStructure (tateBase R p) p (cuspData R p ζ v w)) :
    (g.pullbackLevelP p).evalCusp R ζ v w = g.toFun (tateBase R p) (isUnit_Δ_tateBase R p) := by
  rw [KatzLevelPForm.evalCusp_eq _ R ζ v w h]
  rfl

section Cycl

variable (R₀ : Type u) [CommRing R₀] (p : ℕ)

abbrev cyclRing : Type u := AdjoinRoot (Polynomial.cyclotomic p R₀)

theorem cyclRing_root_pow : (AdjoinRoot.root (Polynomial.cyclotomic p R₀)) ^ p = 1 := by
  have hdvd : Polynomial.cyclotomic p R₀ ∣ X ^ p - 1 := Polynomial.cyclotomic.dvd_X_pow_sub_one p R₀
  have h0 : AdjoinRoot.mk (Polynomial.cyclotomic p R₀) (X ^ p - 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr hdvd
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h0
  exact h0

variable [NeZero p]

def cyclZeta : (cyclRing R₀ p)ˣ :=
  Units.mkOfMulEqOne (AdjoinRoot.root (Polynomial.cyclotomic p R₀))
    ((AdjoinRoot.root (Polynomial.cyclotomic p R₀)) ^ (p - 1)) (by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne p))]
      exact cyclRing_root_pow R₀ p)

@[simp] theorem val_cyclZeta :
    (cyclZeta R₀ p : cyclRing R₀ p) = AdjoinRoot.root (Polynomial.cyclotomic p R₀) := rfl

theorem cyclZeta_pow_eq_one : cyclZeta R₀ p ^ p = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, val_cyclZeta, Units.val_one]; exact cyclRing_root_pow R₀ p)

theorem sum_cyclZeta_pow_eq_zero [hp : Fact p.Prime] :
    ∑ i ∈ Finset.range p, (cyclZeta R₀ p : cyclRing R₀ p) ^ i = 0 := by
  have key : ∀ (S : Type u) [CommRing S] [Algebra R₀ S] (x : S),
      Polynomial.aeval x (Polynomial.cyclotomic p R₀) = ∑ i ∈ Finset.range p, x ^ i := by
    intro S _ _ x
    rw [Polynomial.cyclotomic_prime R₀ p, map_sum]
    simp only [map_pow, Polynomial.aeval_X]
  show ∑ i ∈ Finset.range p, (AdjoinRoot.root (Polynomial.cyclotomic p R₀)) ^ i = 0
  rw [← key, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

end Cycl

namespace KatzGamma0Form

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} [NeZero p] {k : ℤ}

def qExpansion (φ : KatzGamma0Form R₀ p k) : LaurentSeries (cyclRing R₀ p) :=
  φ.toKatzLevelPForm.evalCusp (cyclRing R₀ p) (cyclZeta R₀ p) ![1, 0] ![0, 1]

theorem qExpansion_def (φ : KatzGamma0Form R₀ p k) :
    φ.qExpansion = φ.toKatzLevelPForm.evalCusp (cyclRing R₀ p) (cyclZeta R₀ p) ![1, 0] ![0, 1] :=
  rfl

end KatzGamma0Form

end ModularCurve

end
