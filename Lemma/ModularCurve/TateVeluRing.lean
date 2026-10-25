import Mathlib
import Lemma.ModularCurve.TateSlots
import Lemma.ModularCurve.LaurentCoeff
import Lemma.ModularCurve.KatzLevelPCusps
import Lemma.WeierstrassCurve.Velu
import Lemma.WeierstrassCurve.VeluPointMap
import Def.WeierstrassCurve_VariableChangePointEquiv
import Def.ModularCurve_TateVeluRing

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve

namespace ModularCurve.TateVeluRing

section Naturality

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)

theorem coeff_ofPowerSeries_of_neg (g : PowerSeries A) {n : ℤ} (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ A g).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact absurd (Int.natCast_nonneg m) (not_le.mpr hn)

theorem coeffMap_ofPowerSeries (g : PowerSeries A) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ A g) = HahnSeries.ofPowerSeries ℤ B (g.map f) := by
  ext n
  rw [coeffMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [coeff_ofPowerSeries_of_neg g hn, coeff_ofPowerSeries_of_neg _ hn, map_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simp only [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

theorem coeffMap_ofPowerSeries_mk (F : ℕ → A) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ A (PowerSeries.mk F)) =
      HahnSeries.ofPowerSeries ℤ B (PowerSeries.mk fun m => f (F m)) := by
  rw [coeffMap_ofPowerSeries, show PowerSeries.map f (PowerSeries.mk F) = PowerSeries.mk (fun m => f (F m)) from
    PowerSeries.ext fun m => by simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]]

theorem coeffMap_C (a : A) : coeffMap f (HahnSeries.C a) = HahnSeries.C (f a) :=
  HahnSeries.map_C a f

theorem coeffMap_comp_laurentOfInt : (coeffMap f).comp (laurentOfInt A) = laurentOfInt B := by
  refine RingHom.ext fun g => ?_
  rw [RingHom.comp_apply, laurentOfInt_apply, laurentOfInt_apply, coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]

theorem tateLaurent_map_coeffMap : (tateLaurent A).map (coeffMap f) = tateLaurent B := by
  rw [tateLaurent, tateLaurent, WeierstrassCurve.map_map, coeffMap_comp_laurentOfInt]

theorem map_ringInverse_of_isUnit {a : A} (ha : IsUnit a) : f (Ring.inverse a) = Ring.inverse (f a) := by
  have h1 : f (Ring.inverse a) * f a = 1 := by rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
  exact ((Ring.eq_mul_inverse_iff_mul_eq _ 1 _ (ha.map f)).mpr h1).trans (one_mul _)

theorem tateToricPoint_map (p : ℕ) (c : Aˣ) (hc : IsUnit (1 - (c : A))) :
    Prod.map (coeffMap f) (coeffMap f) (tateToricPoint A p c) = tateToricPoint B p (Units.map (f : A →* B) c) := by
  have hcoe : ((Units.map (f : A →* B) c : Bˣ) : B) = f (c : A) := rfl
  have hinv : f (Ring.inverse (1 - (c : A))) = Ring.inverse (1 - (Units.map (f : A →* B) c : B)) := by
    rw [map_ringInverse_of_isUnit f hc, map_sub, map_one, hcoe]
  have hcinv : f ((c⁻¹ : Aˣ) : A) = ((Units.map (f : A →* B) c)⁻¹ : Bˣ) := rfl
  refine Prod.ext ?_ ?_
  · simp only [Prod.map_fst, tateToricPoint_fst, coeffMap_ofPowerSeries_mk]
    congr 1; ext m; simp only [PowerSeries.coeff_mk]
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos hm, map_mul, map_pow, hinv, hcoe]
    · rw [if_neg hm, if_neg hm]
      simp only [map_sub, map_sum, map_mul, map_natCast, map_add, map_pow, map_ofNat, hcinv, hcoe,
        apply_ite f, map_zero]
  · simp only [Prod.map_snd, tateToricPoint_snd, coeffMap_ofPowerSeries_mk]
    congr 1; ext m; simp only [PowerSeries.coeff_mk]
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos hm, map_mul, map_pow, map_pow, hinv, hcoe]
    · rw [if_neg hm, if_neg hm]
      simp only [map_sub, map_sum, map_mul, map_natCast, map_add, map_pow, hcinv, hcoe,
        apply_ite f, map_zero]

end Naturality

section VeluR

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A)


theorem veluXR_eq_veluX {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F)) (x : F) :
    veluXR W S x = W.veluX S x := by
  unfold veluXR WeierstrassCurve.veluX
  simp only [Ring.inverse_eq_inv', div_eq_mul_inv, inv_pow]

theorem veluYR_eq_veluY {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F)) (x y : F) :
    veluYR W S x y = W.veluY S x y := by
  unfold veluYR WeierstrassCurve.veluY
  simp only [Ring.inverse_eq_inv', div_eq_mul_inv, inv_pow]

variable {B : Type*} [CommRing B] (f : A →+* B)

theorem map_veluT (x y : A) : (W.map f).veluT (f x) (f y) = f (W.veluT x y) := by
  simp only [WeierstrassCurve.veluT, WeierstrassCurve.veluGx, WeierstrassCurve.veluGy,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, map_sub, map_mul, map_add, map_neg, map_pow, map_ofNat]

theorem map_veluU (x y : A) : (W.map f).veluU (f x) (f y) = f (W.veluU x y) := by
  simp only [WeierstrassCurve.veluU, WeierstrassCurve.veluGy,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_mul, map_add, map_neg, map_pow, map_ofNat]

theorem map_veluGx (x y : A) : (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp only [WeierstrassCurve.veluGx, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₄, map_sub, map_mul, map_add, map_pow, map_ofNat]

theorem map_veluGy (x y : A) : (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
  simp only [WeierstrassCurve.veluGy, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
    map_mul, map_add, map_neg, map_ofNat]

theorem map_veluXR [DecidableEq (B × B)] (S : Finset (A × A)) (x : A)
    (hinj : Set.InjOn (Prod.map f f) S) (hunit : ∀ Q ∈ S, IsUnit (x - Q.1)) :
    f (veluXR W S x) = veluXR (W.map f) (S.image (Prod.map f f)) (f x) := by
  unfold veluXR
  rw [Finset.sum_image hinj, map_add, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun Q hQ => ?_)
  have h := map_ringInverse_of_isUnit f (hunit Q hQ)
  rw [map_sub] at h
  simp only [Prod.map_fst, Prod.map_snd, map_veluT, map_veluU, map_add, map_mul, map_pow, h]

theorem map_veluYR [DecidableEq (B × B)] (S : Finset (A × A)) (x y : A)
    (hinj : Set.InjOn (Prod.map f f) S) (hunit : ∀ Q ∈ S, IsUnit (x - Q.1)) :
    f (veluYR W S x y) = veluYR (W.map f) (S.image (Prod.map f f)) (f x) (f y) := by
  unfold veluYR
  rw [Finset.sum_image hinj, map_sub, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun Q hQ => ?_)
  have h := map_ringInverse_of_isUnit f (hunit Q hQ)
  rw [map_sub] at h
  simp only [Prod.map_fst, Prod.map_snd, map_veluT, map_veluU, map_veluGx, map_veluGy,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_add, map_sub, map_mul, map_pow, map_ofNat, h]

end VeluR

section VcR

variable {A : Type*} [CommRing A]


theorem vcXInvR_eq {F : Type*} [Field F] (C : WeierstrassCurve.VariableChange F) (x : F) :
    vcXInvR C x = WeierstrassCurve.Affine.vcXInv C x := rfl

theorem vcYInvR_eq {F : Type*} [Field F] (C : WeierstrassCurve.VariableChange F) (x y : F) :
    vcYInvR C x y = WeierstrassCurve.Affine.vcYInv C x y := rfl

variable {B : Type*} [CommRing B] (f : A →+* B)

theorem map_vcXInvR (C : WeierstrassCurve.VariableChange A) (x : A) :
    f (vcXInvR C x) = vcXInvR (C.map f) (f x) := by
  simp only [vcXInvR, WeierstrassCurve.VariableChange.map_u, WeierstrassCurve.VariableChange.map_r, map_mul,
    map_sub, map_pow, Units.coe_map_inv, MonoidHom.coe_coe]

theorem map_vcYInvR (C : WeierstrassCurve.VariableChange A) (x y : A) :
    f (vcYInvR C x y) = vcYInvR (C.map f) (f x) (f y) := by
  simp only [vcYInvR, WeierstrassCurve.VariableChange.map_u, WeierstrassCurve.VariableChange.map_r,
    WeierstrassCurve.VariableChange.map_s, WeierstrassCurve.VariableChange.map_t, map_mul, map_sub, map_pow,
    Units.coe_map_inv, MonoidHom.coe_coe]

end VcR

section LaurentUnits

variable {A : Type*} [CommRing A]

theorem isUnit_ofPowerSeries_mk {F : ℕ → A} (h0 : IsUnit (F 0)) :
    IsUnit (HahnSeries.ofPowerSeries ℤ A (PowerSeries.mk F)) := by
  refine (PowerSeries.isUnit_iff_constantCoeff.mpr ?_).map _
  rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]


theorem tateToricPoint_fst_eq_mk (p : ℕ) (c : Aˣ) :
    (tateToricPoint A p c).1 = HahnSeries.ofPowerSeries ℤ A (PowerSeries.mk (toricXCoeff p c)) := rfl

theorem tateToricPoint_fst_sub (p : ℕ) (c d : Aˣ) :
    (tateToricPoint A p c).1 - (tateToricPoint A p d).1 =
      HahnSeries.ofPowerSeries ℤ A (PowerSeries.mk fun m => toricXCoeff p c m - toricXCoeff p d m) := by
  rw [tateToricPoint_fst_eq_mk, tateToricPoint_fst_eq_mk, ← map_sub,
    show PowerSeries.mk (toricXCoeff p c) - PowerSeries.mk (toricXCoeff p d) =
      PowerSeries.mk (fun m => toricXCoeff p c m - toricXCoeff p d m) from
    PowerSeries.ext fun m => by simp only [map_sub, PowerSeries.coeff_mk]]

theorem toricXCoeff_zero (p : ℕ) (c : Aˣ) : toricXCoeff p c 0 = (c : A) * Ring.inverse (1 - (c : A)) ^ 2 := by
  simp [toricXCoeff]

theorem head_sub_head (c d wc wd : A) (hc : wc * (1 - c) = 1) (hd : wd * (1 - d) = 1) :
    c * wc ^ 2 - d * wd ^ 2 = wc ^ 2 * wd ^ 2 * ((c - d) * (1 - c * d)) := by
  linear_combination (-(c * wc ^ 2 * (wd * (1 - d) + 1))) * hd + (d * wd ^ 2 * (wc * (1 - c) + 1)) * hc

theorem isUnit_tateToricPoint_fst_sub (p : ℕ) (c d : Aˣ) (hc : IsUnit (1 - (c : A))) (hd : IsUnit (1 - (d : A)))
    (hcd : IsUnit ((c : A) - d)) (hcd' : IsUnit (1 - (c : A) * d)) :
    IsUnit ((tateToricPoint A p c).1 - (tateToricPoint A p d).1) := by
  rw [tateToricPoint_fst_sub]
  refine isUnit_ofPowerSeries_mk ?_
  simp only [toricXCoeff_zero]
  rw [head_sub_head (c : A) d _ _ (Ring.inverse_mul_cancel _ hc) (Ring.inverse_mul_cancel _ hd)]
  exact (((hc.ringInverse.pow 2).mul (hd.ringInverse.pow 2)).mul (hcd.mul hcd'))

end LaurentUnits

end ModularCurve.TateVeluRing

end
