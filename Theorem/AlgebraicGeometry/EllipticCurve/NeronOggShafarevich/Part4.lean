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
import Def.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich.Part3
/-!
# The easy direction of the Néron–Ogg–Shafarevich criterion

This file proves that prime-to-residue-characteristic torsion of an elliptic curve with good
reduction is fixed by inertia, using the elementary valuation filtration at the origin.
-/


namespace MetaMathlibExt

open scoped WeierstrassCurve.Affine

lemma nos_neg_coordinate {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x y : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hx : x ∉ A)
    (h : WeierstrassCurve.Affine.Equation W x y) :
    A.valuation (-x / WeierstrassCurve.Affine.negY W x y + -x / y) <
      A.valuation (-x / y) := by
  obtain ⟨hy, hznonunit, hw⟩ :=
    nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx h
  have hzlt : A.valuation (-x / y) < 1 := A.mem_nonunits_iff.mpr hznonunit
  have hx0 : x ≠ 0 := fun hzero ↦ hx (hzero ▸ A.zero_mem)
  have hz0 : -x / y ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx0) hy
  have hneg : WeierstrassCurve.Affine.negY W x y ≠ 0 := by
    intro hzero
    have hyneg : WeierstrassCurve.Affine.negY W x y ∈ A := hzero ▸ A.zero_mem
    exact hx (nos_x_mem_of_y_mem W A ha₁ ha₂ ha₃ ha₄ ha₆ hyneg
      ((WeierstrassCurve.Affine.equation_neg x y).mpr h))
  have hform := nos_neg_z_formula W hy hneg
  obtain ⟨_, herr, _⟩ := nos_neg_parameter W A ha₁ ha₃ hzlt hz0 hw
  rw [hform]
  exact herr

lemma nos_add_parameter {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    {P Q : WeierstrassCurve.Affine.Point W} {s : A.ValueGroup}
    (hP : nosNear W A P) (hQ : nosNear W A Q) (hs0 : 0 < s)
    (hzP : A.valuation (nosZ W P) = s) (hzQ : A.valuation (nosZ W Q) ≤ s) :
    nosNear W A (P + Q) ∧
      A.valuation (nosZ W (P + Q) - nosZ W P - nosZ W Q) < s := by
  let v := A.valuation
  cases P with
  | zero =>
      exfalso
      have hz : (0 : A.ValueGroup) = s := by simpa only [nosZ, Valuation.map_zero] using hzP
      exact (ne_of_gt hs0) hz.symm
  | some x₁ y₁ hp₁ =>
    change x₁ ∉ A at hP
    change v (-x₁ / y₁) = s at hzP
    cases Q with
    | zero =>
        constructor
        · exact hP
        · change v ((-x₁ / y₁) - (-x₁ / y₁) - 0) < s
          simpa only [sub_self, zero_sub, Valuation.map_zero] using hs0
    | some x₂ y₂ hp₂ =>
      change x₂ ∉ A at hQ
      change v (-x₂ / y₂) ≤ s at hzQ
      have h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁ := hp₁.1
      have h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂ := hp₂.1
      by_cases hver : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hver.1 hver.2]
        constructor
        · trivial
        · have herr := nos_neg_coordinate W A ha₁ ha₂ ha₃ ha₄ ha₆ hQ h₂
          have herrs := herr.trans_le hzQ
          change v (0 - (-x₁ / y₁) - (-x₂ / y₂)) < s
          rw [hver.1, hver.2]
          rw [show 0 - (-x₂ / WeierstrassCurve.Affine.negY W x₂ y₂) - (-x₂ / y₂) =
            -((-x₂ / WeierstrassCurve.Affine.negY W x₂ y₂) + -x₂ / y₂) by ring,
            v.map_neg]
          exact herrs
      · by_cases hx : x₁ = x₂
        · have hyne : y₁ ≠ WeierstrassCurve.Affine.negY W x₂ y₂ := fun hy ↦ hver ⟨hx, hy⟩
          have hyeq : y₁ = y₂ := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hyne
          subst x₂
          subst y₂
          have hadd := nos_tangent_add W A ha₁ ha₂ ha₃ ha₄ ha₆ h₁ hP hyne hs0 hzP
          rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne]
          simpa only [nosNear, nosZ, WeierstrassCurve.Affine.addY] using hadd
        · have hadd := nos_secant_add W A ha₁ ha₂ ha₃ ha₄ ha₆ h₁ h₂ hP hQ hx hs0 hzP hzQ
          rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
          simpa only [nosNear, nosZ, WeierstrassCurve.Affine.addY] using hadd

lemma nos_nsmul_parameter {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    {P : WeierstrassCurve.Affine.Point W} {s : A.ValueGroup}
    (hP : nosNear W A P) (hs0 : 0 < s) (hzP : A.valuation (nosZ W P) = s) :
    ∀ m : ℕ, nosNear W A (m • P) ∧
      A.valuation (nosZ W (m • P) - (m : K) * nosZ W P) < s ∧
      A.valuation (nosZ W (m • P)) ≤ s := by
  let v := A.valuation
  intro m
  induction m with
  | zero =>
      constructor
      · trivial
      constructor
      · simpa only [zero_nsmul, nosZ, Nat.cast_zero, zero_mul, sub_zero,
          Valuation.map_zero] using hs0
      · simpa only [zero_nsmul, nosZ, Valuation.map_zero] using hs0.le
  | succ m ih =>
      obtain ⟨hnear, herr, hzle⟩ := ih
      obtain ⟨haddnear, hadderr⟩ :=
        nos_add_parameter W A ha₁ ha₂ ha₃ ha₄ ha₆ hP hnear hs0 hzP hzle
      have htotal : v (nosZ W (P + m • P) - ((m + 1 : ℕ) : K) * nosZ W P) < s := by
        rw [show nosZ W (P + m • P) - ((m + 1 : ℕ) : K) * nosZ W P =
          (nosZ W (P + m • P) - nosZ W P - nosZ W (m • P)) +
            (nosZ W (m • P) - (m : K) * nosZ W P) by
          rw [Nat.cast_add, Nat.cast_one]
          ring]
        exact v.map_add_lt hadderr herr
      have hnat : v ((m + 1 : ℕ) : K) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (natCast_mem A (m + 1))
      have hcoeff : v (((m + 1 : ℕ) : K) * nosZ W P) ≤ s := by
        simp only [v, Valuation.map_mul]
        rw [hzP]
        exact mul_le_of_le_one_left zero_le hnat
      have hnextle : v (nosZ W (P + m • P)) ≤ s := by
        rw [show nosZ W (P + m • P) =
          (nosZ W (P + m • P) - ((m + 1 : ℕ) : K) * nosZ W P) +
            ((m + 1 : ℕ) : K) * nosZ W P by ring]
        exact (v.map_add _ _).trans (max_le htotal.le hcoeff)
      rw [succ_nsmul, add_comm]
      exact ⟨haddnear, htotal, hnextle⟩

lemma nos_no_torsion {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (n : ℕ)
    (hn : ∃ u : A, (u : K) = (n : K) ∧ IsUnit u)
    {P : WeierstrassCurve.Affine.Point W} (hP : nosNear W A P)
    (htors : n • P = 0) : P = 0 := by
  let v := A.valuation
  obtain ⟨u, hu, huunit⟩ := hn
  have hnval : v (n : K) = 1 := by
    rw [← hu]
    exact (A.valuation_eq_one_iff u).mp huunit
  cases P with
  | zero => rfl
  | some x y hp =>
      have hPnear : nosNear W A (.some x y hp) := hP
      change x ∉ A at hP
      have h := hp.1
      obtain ⟨hy, _, _⟩ :=
        nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hP h
      let z : K := -x / y
      let s : A.ValueGroup := v z
      have hz0 : z ≠ 0 := by
        apply div_ne_zero
        · exact neg_ne_zero.mpr fun hx ↦ hP (hx ▸ A.zero_mem)
        · exact hy
      have hs0 : 0 < s := by
        change 0 < v z
        exact (v.ne_zero_iff.mpr hz0).bot_lt
      have hzP : v (nosZ W (.some x y hp)) = s := rfl
      obtain ⟨_, herr, _⟩ :=
        nos_nsmul_parameter W A ha₁ ha₂ ha₃ ha₄ ha₆ hPnear hs0 hzP n
      rw [htors] at herr
      change v (0 - (n : K) * z) < s at herr
      rw [zero_sub, v.map_neg, v.map_mul, hnval, one_mul] at herr
      exact (lt_irrefl s herr).elim

end MetaMathlibExt
