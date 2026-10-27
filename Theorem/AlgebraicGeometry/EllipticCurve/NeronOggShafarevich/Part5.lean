/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Valuation.LocalSubring
import Def.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich.Part4
/-!
# The easy direction of the Néron–Ogg–Shafarevich criterion

This file proves that prime-to-residue-characteristic torsion of an elliptic curve with good
reduction is fixed by inertia, using the elementary valuation filtration at the origin.
-/


namespace MetaMathlibExt

open scoped WeierstrassCurve.Affine

lemma nos_integral_curve_map {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A)
    (ha₃ : W.a₃ ∈ A) (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) :
    (nosIntegralCurve W A ha₁ ha₂ ha₃ ha₄ ha₆).map A.subtype = W := by
  ext <;> rfl

lemma nos_partial_unit {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A)
    (ha₃ : W.a₃ ∈ A) (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hΔ : ∃ d : A, (d : K) = W.Δ ∧ IsUnit d) {x y : K}
    (hx : x ∈ A) (hy : y ∈ A) (h : WeierstrassCurve.Affine.Equation W x y) :
    (∃ t : A, (t : K) = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ∧ IsUnit t) ∨
      ∃ t : A, (t : K) = 2 * y + W.a₁ * x + W.a₃ ∧ IsUnit t := by
  let WA := nosIntegralCurve W A ha₁ ha₂ ha₃ ha₄ ha₆
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨y, hy⟩
  let fX : A := WA.a₁ * yA - (3 * xA ^ 2 + 2 * WA.a₂ * xA + WA.a₄)
  let fY : A := 2 * yA + WA.a₁ * xA + WA.a₃
  have hmap : WA.map A.subtype = W :=
    nos_integral_curve_map W A ha₁ ha₂ ha₃ ha₄ ha₆
  have heqA : WeierstrassCurve.Affine.Equation WA xA yA := by
    rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
    apply Subtype.ext
    exact h
  have hΔcoe : ((WA.Δ : A) : K) = W.Δ := by
    calc
      ((WA.Δ : A) : K) = (WA.map A.subtype).Δ := (WA.map_Δ A.subtype).symm
      _ = W.Δ := congrArg WeierstrassCurve.Δ hmap
  obtain ⟨d, hd, hdunit⟩ := hΔ
  have hdWA : d = WA.Δ := Subtype.ext (hd.trans hΔcoe.symm)
  have hWAunit : IsUnit WA.Δ := by
    rw [← hdWA]
    exact hdunit
  let Wred := WA.map (IsLocalRing.residue A)
  have hredΔ : Wred.Δ ≠ 0 := by
    change (WA.map (IsLocalRing.residue A)).Δ ≠ 0
    rw [WA.map_Δ]
    exact (hWAunit.map (IsLocalRing.residue A)).ne_zero
  have heqred : WeierstrassCurve.Affine.Equation Wred
      (IsLocalRing.residue A xA) (IsLocalRing.residue A yA) :=
    heqA.map (IsLocalRing.residue A)
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (W := Wred) hredΔ).mp heqred
  rcases ((WeierstrassCurve.Affine.nonsingular_iff' (W := Wred) _ _).mp hns).2 with hX | hY
  · left
    refine ⟨fX, ?_, (IsLocalRing.residue_ne_zero_iff_isUnit fX).mp ?_⟩
    · rfl
    · simpa only [fX, Wred, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₄, map_sub, map_add, map_mul, map_pow, map_ofNat] using hX
  · right
    refine ⟨fY, ?_, (IsLocalRing.residue_ne_zero_iff_isUnit fY).mp ?_⟩
    · rfl
    · simpa only [fY, Wred, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
        map_add, map_mul, map_ofNat] using hY

lemma nos_secant_alternative {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ y₁ x₂ y₂ : K} (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂) :
    (y₂ - y₁) * (-(y₂ + y₁ + W.a₁ * x₂ + W.a₃)) =
      (x₂ - x₁) * (W.a₁ * y₁ -
        (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2 + W.a₂ * (x₂ + x₁) + W.a₄)) := by
  rw [WeierstrassCurve.Affine.equation_iff (W := W) x₁ y₁] at h₁
  rw [WeierstrassCurve.Affine.equation_iff (W := W) x₂ y₂] at h₂
  linear_combination h₁ - h₂

lemma nos_addX_nonintegral {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x₁ x₂ l : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hl : 1 < A.valuation l) : WeierstrassCurve.Affine.addX W x₁ x₂ l ∉ A := by
  let v := A.valuation
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₂v : v W.a₂ ≤ 1 := (A.valuation_le_one_iff W.a₂).mpr ha₂
  have hx₁v : v x₁ ≤ 1 := (A.valuation_le_one_iff x₁).mpr hx₁
  have hx₂v : v x₂ ≤ 1 := (A.valuation_le_one_iff x₂).mpr hx₂
  have hl0 : 0 < v l := zero_lt_one.trans hl
  have hll : v l < (v l) ^ 2 := by
    rw [pow_two]
    exact lt_mul_of_one_lt_right hl0 hl
  have ha₁l : v (W.a₁ * l) < (v l) ^ 2 := by
    rw [v.map_mul]
    exact (mul_le_mul_of_nonneg_right ha₁v zero_le).trans_lt (by simpa using hll)
  have hone : (1 : A.ValueGroup) < (v l) ^ 2 := by
    exact hl.trans hll
  have hrest : v (W.a₁ * l - W.a₂ - x₁ - x₂) < (v l) ^ 2 :=
    v.map_sub_lt (v.map_sub_lt (v.map_sub_lt ha₁l (ha₂v.trans_lt hone))
      (hx₁v.trans_lt hone)) (hx₂v.trans_lt hone)
  have hval : v (WeierstrassCurve.Affine.addX W x₁ x₂ l) = (v l) ^ 2 := by
    change v (l ^ 2 + W.a₁ * l - W.a₂ - x₁ - x₂) = (v l) ^ 2
    rw [show l ^ 2 + W.a₁ * l - W.a₂ - x₁ - x₂ =
      l ^ 2 + (W.a₁ * l - W.a₂ - x₁ - x₂) by ring]
    rw [v.map_add_eq_of_lt_left]
    · rw [v.map_pow]
    · rwa [v.map_pow]
  rw [← A.valuation_le_one_iff]
  rw [hval]
  exact (not_le_of_gt hone)

lemma nos_secant_slope {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hΔ : ∃ d : A, (d : K) = W.Δ ∧ IsUnit d)
    {x₁ y₁ x₂ y₂ : K} (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hx : x₁ ≠ x₂) (hxc : A.valuation (x₂ - x₁) < 1)
    (hyc : A.valuation (y₂ - y₁) < 1) :
    1 < A.valuation
      (WeierstrassCurve.Affine.slope W x₁ x₂ y₁
        (WeierstrassCurve.Affine.negY W x₂ y₂)) := by
  let v := A.valuation
  let N := -(y₂ + y₁ + W.a₁ * x₂ + W.a₃)
  let M := W.a₁ * y₁ -
    (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2 + W.a₂ * (x₂ + x₁) + W.a₄)
  let fX := W.a₁ * y₁ - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄)
  let fY := 2 * y₁ + W.a₁ * x₁ + W.a₃
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have hdx0 : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr hx.symm
  have hslope : WeierstrassCurve.Affine.slope W x₁ x₂ y₁
      (WeierstrassCurve.Affine.negY W x₂ y₂) = N / (x₂ - x₁) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    simp only [N, WeierstrassCurve.Affine.negY]
    field_simp [hdx0, sub_ne_zero.mpr hx]
    ring
  rcases nos_partial_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hΔ hx₁ hy₁ h₁ with hXu | hYu
  · obtain ⟨t, ht, htunit⟩ := hXu
    have hfX : v fX = 1 := by
      change v (W.a₁ * y₁ - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄)) = 1
      rw [← ht]
      exact (A.valuation_eq_one_iff t).mp htunit
    have hfactor : x₂ + 2 * x₁ + W.a₂ ∈ A :=
      A.toSubring.add_mem
        (A.toSubring.add_mem hx₂ (A.toSubring.mul_mem (natCast_mem A 2) hx₁)) ha₂
    have hfactorv : v (x₂ + 2 * x₁ + W.a₂) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr hfactor
    have hMerr : v (M - fX) < 1 := by
      rw [show M - fX = -(x₂ - x₁) * (x₂ + 2 * x₁ + W.a₂) by
        simp only [M, fX]
        ring,
        v.map_mul, v.map_neg]
      exact mul_lt_one_of_lt_of_le hxc hfactorv
    have hM : v M = 1 := by
      calc
        v M = v fX := v.map_eq_of_sub_lt (by rwa [hfX])
        _ = 1 := hfX
    have hM0 : M ≠ 0 := by
      apply v.ne_zero_iff.mp
      rw [hM]
      exact one_ne_zero
    have halt := nos_secant_alternative W h₁ h₂
    change (y₂ - y₁) * N = (x₂ - x₁) * M at halt
    have hdy0 : y₂ - y₁ ≠ 0 := by
      intro hdy
      rw [hdy, zero_mul] at halt
      exact (mul_ne_zero hdx0 hM0) halt.symm
    have hratio : N / (x₂ - x₁) = M / (y₂ - y₁) := by
      apply (div_eq_div_iff hdx0 hdy0).mpr
      rw [mul_comm N, halt, mul_comm]
    rw [hslope, hratio, v.map_div, hM]
    exact (one_lt_div₀ (v.pos_iff.mpr hdy0)).mpr hyc
  · obtain ⟨t, ht, htunit⟩ := hYu
    have hfY : v fY = 1 := by
      change v (2 * y₁ + W.a₁ * x₁ + W.a₃) = 1
      rw [← ht]
      exact (A.valuation_eq_one_iff t).mp htunit
    have ha₁dx : v (W.a₁ * (x₂ - x₁)) < 1 := by
      rw [v.map_mul]
      exact mul_lt_of_le_one_of_lt ha₁v hxc
    have hNerr : v (N - (-fY)) < 1 := by
      rw [show N - (-fY) = -(y₂ - y₁) - W.a₁ * (x₂ - x₁) by
        simp only [N, fY]
        ring]
      exact v.map_sub_lt ((v.map_neg _).trans_lt hyc) ha₁dx
    have hN : v N = 1 := by
      calc
        v N = v (-fY) := v.map_eq_of_sub_lt (by
          rw [v.map_neg, hfY]
          exact hNerr)
        _ = 1 := by rw [v.map_neg, hfY]
    rw [hslope, v.map_div, hN]
    exact (one_lt_div₀ (v.pos_iff.mpr hdx0)).mpr hxc

lemma nos_tangent_slope {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hΔ : ∃ d : A, (d : K) = W.Δ ∧ IsUnit d)
    {x y₁ y₂ : K} (h₁ : WeierstrassCurve.Affine.Equation W x y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x y₂)
    (hx : x ∈ A) (hy₁ : y₁ ∈ A) (hyne : y₁ ≠ y₂)
    (hyc : A.valuation (y₂ - y₁) < 1) :
    1 < A.valuation (WeierstrassCurve.Affine.slope W x x y₁ y₁) := by
  let v := A.valuation
  let fX := W.a₁ * y₁ - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
  let fY := 2 * y₁ + W.a₁ * x + W.a₃
  have hrel : y₁ = WeierstrassCurve.Affine.negY W x y₂ := by
    by_contra hrel
    exact hyne (WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ rfl hrel)
  have hrel' : WeierstrassCurve.Affine.negY W x y₁ = y₂ := by
    rw [hrel, WeierstrassCurve.Affine.negY_negY]
  have hyself : y₁ ≠ WeierstrassCurve.Affine.negY W x y₁ := by
    rwa [hrel']
  have hdeneq : fY = y₁ - WeierstrassCurve.Affine.negY W x y₁ := by
    simp only [fY, WeierstrassCurve.Affine.negY]
    ring
  have hden : v fY < 1 := by
    rw [hdeneq, hrel', v.map_sub_swap]
    exact hyc
  have hden0 : fY ≠ 0 := by
    rw [hdeneq, hrel']
    exact sub_ne_zero.mpr hyne
  rcases nos_partial_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hΔ hx hy₁ h₁ with hXu | hYu
  · obtain ⟨t, ht, htunit⟩ := hXu
    have hfX : v fX = 1 := by
      change v (W.a₁ * y₁ - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = 1
      rw [← ht]
      exact (A.valuation_eq_one_iff t).mp htunit
    rw [WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval rfl hyself,
      WeierstrassCurve.Affine.evalEval_polynomialX,
      WeierstrassCurve.Affine.evalEval_polynomialY]
    change 1 < v (-fX / fY)
    rw [v.map_div, v.map_neg, hfX]
    exact (one_lt_div₀ (v.pos_iff.mpr hden0)).mpr hden
  · obtain ⟨t, ht, htunit⟩ := hYu
    have hfY : v fY = 1 := by
      change v (2 * y₁ + W.a₁ * x + W.a₃) = 1
      rw [← ht]
      exact (A.valuation_eq_one_iff t).mp htunit
    rw [hfY] at hden
    exact (lt_irrefl 1 hden).elim

lemma nos_congruent_sub_near {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hΔ : ∃ d : A, (d : K) = W.Δ ∧ IsUnit d)
    {x₁ y₁ x₂ y₂ : K} {hp₁ : WeierstrassCurve.Affine.Nonsingular W x₁ y₁}
    {hp₂ : WeierstrassCurve.Affine.Nonsingular W x₂ y₂}
    (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₂ : y₂ ∈ A)
    (hxc : A.valuation (x₂ - x₁) < 1) (hyc : A.valuation (y₂ - y₁) < 1) :
    nosNear W A
      (WeierstrassCurve.Affine.Point.some x₁ y₁ hp₁ -
        WeierstrassCurve.Affine.Point.some x₂ y₂ hp₂) := by
  by_cases hsame : x₁ = x₂ ∧ y₁ = y₂
  · obtain ⟨rfl, rfl⟩ := hsame
    simp only [sub_self]
    trivial
  by_cases hx : x₁ = x₂
  · subst x₂
    have hyne : y₁ ≠ y₂ := fun hy ↦ hsame ⟨rfl, hy⟩
    have hrel : y₁ = WeierstrassCurve.Affine.negY W x₁ y₂ := by
      by_contra hrel
      exact hyne (WeierstrassCurve.Affine.Y_eq_of_Y_ne hp₁.1 hp₂.1 rfl hrel)
    have hrel' : WeierstrassCurve.Affine.negY W x₁ y₁ = y₂ := by
      rw [hrel, WeierstrassCurve.Affine.negY_negY]
    have hyself : y₁ ≠ WeierstrassCurve.Affine.negY W x₁ y₁ := by
      rwa [hrel']
    have hneg : -WeierstrassCurve.Affine.Point.some x₁ y₂ hp₂ =
        WeierstrassCurve.Affine.Point.some x₁ y₁ hp₁ := by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      simp only [WeierstrassCurve.Affine.Point.some.injEq, true_and]
      exact hrel.symm
    rw [sub_eq_add_neg, hneg,
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyself]
    change WeierstrassCurve.Affine.addX W x₁ x₁
      (WeierstrassCurve.Affine.slope W x₁ x₁ y₁ y₁) ∉ A
    apply nos_addX_nonintegral W A ha₁ ha₂ hx₁ hx₁
    exact nos_tangent_slope W A ha₁ ha₂ ha₃ ha₄ ha₆ hΔ hp₁.1 hp₂.1
      hx₁ hy₁ hyne hyc
  · rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.add_of_X_ne hx]
    change WeierstrassCurve.Affine.addX W x₁ x₂
      (WeierstrassCurve.Affine.slope W x₁ x₂ y₁
        (WeierstrassCurve.Affine.negY W x₂ y₂)) ∉ A
    apply nos_addX_nonintegral W A ha₁ ha₂ hx₁ hx₂
    exact nos_secant_slope W A ha₁ ha₂ ha₃ ha₄ ha₆ hΔ hp₁.1 hp₂.1
      hx₁ hy₁ hx₂ hx hxc hyc

lemma nos_inertia_congruent {k K : Type*} [Field k] [Field K] [Algebra k K]
    (A : ValuationSubring K) {σ : A.decompositionSubgroup k}
    (hσ : σ ∈ A.inertiaSubgroup k) {a : K} (ha : a ∈ A) :
    (σ : K ≃ₐ[k] K) a ∈ A ∧ A.valuation ((σ : K ≃ₐ[k] K) a - a) < 1 := by
  let aA : A := ⟨a, ha⟩
  let bA : A := σ • aA
  have hb : (bA : K) = (σ : K ≃ₐ[k] K) a := rfl
  have htriv : ∀ z : IsLocalRing.ResidueField A, σ • z = z := by
    intro z
    change MulSemiringAction.toRingAut (A.decompositionSubgroup k)
      (IsLocalRing.ResidueField A) σ = 1 at hσ
    have hz := DFunLike.congr_fun hσ z
    change σ • z = (1 : RingAut (IsLocalRing.ResidueField A)) z at hz
    simpa only [RingAut.one_apply] using hz
  have hres : IsLocalRing.residue A bA = IsLocalRing.residue A aA := by
    rw [show bA = σ • aA from rfl, IsLocalRing.ResidueField.residue_smul, htriv]
  have hmax : bA - aA ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp only [map_sub, hres, sub_self]
  constructor
  · rw [← hb]
    exact bA.2
  · rw [← hb]
    exact A.mem_nonunits_iff.mp (A.coe_mem_nonunits_iff.mpr hmax)

/-- The easy direction of the **Néron–Ogg–Shafarevich criterion**: if `E`
over `Frac R` has good reduction at the discrete valuation ring `R`, then every
element of the inertia subgroup fixes every `n`-torsion point of `E` over the
separable closure, where `n` is nonzero in the residue field.

Note: upstream states torsion membership via `AddSubgroup.torsionBy`, which is
absent from Mathlib; here it is unfolded to the membership condition
`(n : ℤ) • P = 0`, which is definitionally the same condition.

Source: J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed.,
GTM 106, Springer, Theorem VII.7.1.

Proves `Wanted` entry `good_reduction_torsion_unramified`.

Proof: We use Silverman's elementary valuation filtration at the origin in `(z, w)` coordinates,
together with reduction to the nonsingular residue curve; see *The Arithmetic of Elliptic Curves*,
IV.1, VII.3, and VII.7.
-/
theorem good_reduction_torsion_unramified (R : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)]
    (ksep : Type*) [Field ksep] [Algebra k ksep]
    [IsSepClosure k ksep] [DecidableEq ksep]
    (𝒪 : ValuationSubring ksep)
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    ∀ σ ∈ 𝒪.inertiaSubgroup k, ∀ P : (E⁄ksep).Point, (n : ℤ) • P = 0 →
      WeierstrassCurve.Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P := by
  intro σ hσ P htors
  let W : WeierstrassCurve ksep := E⁄ksep
  let _ : W.IsElliptic :=
    ⟨by
      simpa only [W, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange,
        WeierstrassCurve.map_Δ] using E.isUnit_Δ.map (algebraMap k ksep)⟩
  have hcoeff : W.a₁ ∈ 𝒪 ∧ W.a₂ ∈ 𝒪 ∧ W.a₃ ∈ 𝒪 ∧ W.a₄ ∈ 𝒪 ∧
      W.a₆ ∈ 𝒪 ∧ W.Δ ∈ 𝒪 := by
    simpa only [W, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, WeierstrassCurve.map_Δ] using
      nos_coefficients_mem E 𝒪 h𝒪
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆, _⟩ := hcoeff
  have hΔ : ∃ d : 𝒪, (d : ksep) = W.Δ ∧ IsUnit d := by
    simpa only [W, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_Δ] using nos_discriminant_unit E 𝒪 h𝒪
  have hn := nos_nat_unit n 𝒪 h𝒪
  have hnP : n • P = 0 := by
    simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using htors
  cases P with
  | zero => rfl
  | some x y hp =>
      by_cases hx : x ∈ 𝒪
      · have hy := nos_y_mem_of_x_mem W 𝒪 ha₁ ha₂ ha₃ ha₄ ha₆ hx hp.1
        obtain ⟨hσx, hxc'⟩ := nos_inertia_congruent 𝒪 hσ hx
        obtain ⟨hσy, hyc'⟩ := nos_inertia_congruent 𝒪 hσ hy
        let f := (σ : ksep ≃ₐ[k] ksep).toAlgHom
        let Q := WeierstrassCurve.Affine.Point.map f
          (WeierstrassCurve.Affine.Point.some x y hp)
        have hxc : 𝒪.valuation (x - f x) < 1 :=
          (𝒪.valuation.map_sub_swap x (f x)).trans_lt hxc'
        have hyc : 𝒪.valuation (y - f y) < 1 :=
          (𝒪.valuation.map_sub_swap y (f y)).trans_lt hyc'
        have hnear : nosNear W 𝒪
            (Q - WeierstrassCurve.Affine.Point.some x y hp) := by
          change nosNear W 𝒪
            (WeierstrassCurve.Affine.Point.map f
              (WeierstrassCurve.Affine.Point.some x y hp) -
              WeierstrassCurve.Affine.Point.some x y hp)
          rw [WeierstrassCurve.Affine.Point.map_some]
          exact nos_congruent_sub_near W 𝒪 ha₁ ha₂ ha₃ ha₄ ha₆ hΔ
            hσx hσy hx hy hxc hyc
        have hnQ : n • Q = 0 := by
          change n • WeierstrassCurve.Affine.Point.map f
            (WeierstrassCurve.Affine.Point.some x y hp) = 0
          rw [← map_nsmul, hnP, map_zero]
        have hnD : n • (Q - WeierstrassCurve.Affine.Point.some x y hp) = 0 := by
          rw [nsmul_sub, hnQ, hnP, sub_self]
        have hD := nos_no_torsion W 𝒪 ha₁ ha₂ ha₃ ha₄ ha₆ n hn hnear hnD
        exact sub_eq_zero.mp hD
      · have hnear : nosNear W 𝒪 (WeierstrassCurve.Affine.Point.some x y hp) := hx
        have hP := nos_no_torsion W 𝒪 ha₁ ha₂ ha₃ ha₄ ha₆ n hn hnear hnP
        rw [hP, WeierstrassCurve.Affine.Point.map_zero]


end MetaMathlibExt
