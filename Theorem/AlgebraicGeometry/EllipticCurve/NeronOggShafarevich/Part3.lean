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
import Def.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich.Part2
/-!
# The easy direction of the Néron–Ogg–Shafarevich criterion

This file proves that prime-to-residue-characteristic torsion of an elliptic curve with good
reduction is fixed by inertia, using the elementary valuation filtration at the origin.
-/


namespace MetaMathlibExt

open scoped WeierstrassCurve.Affine

lemma nos_local_equation {F : Type*} [Field F] (W : WeierstrassCurve F)
    {x y : F} (h : WeierstrassCurve.Affine.Equation W x y) (hy : y ≠ 0) :
    let z := -x / y
    let w := -1 / y
    nosLocalEquation W z w := by
  rw [WeierstrassCurve.Affine.equation_iff (W := W) x y] at h
  dsimp [nosLocalEquation]
  field_simp [hy]
  linear_combination -h

lemma nos_chord_identity {K : Type*} [CommRing K] (W : WeierstrassCurve K)
    {z₁ z₂ w₁ w₂ : K} (h₁ : nosLocalEquation W z₁ w₁)
    (h₂ : nosLocalEquation W z₂ w₂) :
    (w₂ - w₁) * nosChordU W z₁ w₁ w₂ =
      (z₂ - z₁) * nosChordV W z₁ z₂ w₂ := by
  dsimp [nosLocalEquation, nosChordU, nosChordV] at h₁ h₂ ⊢
  linear_combination h₂ - h₁

lemma nos_line_root {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x y l c : K} (h : WeierstrassCurve.Affine.Equation W x y)
    (hline : y = l * x + c) :
    -x ^ 3 + nosLineQ₂ W l * x ^ 2 + nosLineQ₁ W l c * x + nosLineQ₀ W c = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff (W := W) x y] at h
  rw [hline] at h
  dsimp [nosLineQ₂, nosLineQ₁, nosLineQ₀]
  linear_combination h

lemma nos_secant_symmetric {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ x₂ l c : K}
    (h₁ : -x₁ ^ 3 + nosLineQ₂ W l * x₁ ^ 2 + nosLineQ₁ W l c * x₁ +
      nosLineQ₀ W c = 0)
    (h₂ : -x₂ ^ 3 + nosLineQ₂ W l * x₂ ^ 2 + nosLineQ₁ W l c * x₂ +
      nosLineQ₀ W c = 0)
    (hx : x₁ ≠ x₂) :
    let x₃ := nosLineQ₂ W l - x₁ - x₂
    nosLineQ₁ W l c = -(x₁ * x₂ + x₁ * x₃ + x₂ * x₃) ∧
      nosLineQ₀ W c = x₁ * x₂ * x₃ := by
  dsimp
  have hdx : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hdiff : (x₁ - x₂) *
      (-(x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) + nosLineQ₂ W l * (x₁ + x₂) +
        nosLineQ₁ W l c) = 0 := by
    linear_combination h₁ - h₂
  have hs := (mul_eq_zero.mp hdiff).resolve_left hdx
  constructor
  · linear_combination hs
  · linear_combination h₁ - x₁ * hs

lemma nos_transformed_vieta {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ x₂ x₃ y₁ y₂ y₃ l c : K}
    (hs₁ : nosLineQ₂ W l = x₁ + x₂ + x₃)
    (hs₂ : nosLineQ₁ W l c = -(x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hs₃ : nosLineQ₀ W c = x₁ * x₂ * x₃)
    (hy₁eq : y₁ = l * x₁ + c) (hy₂eq : y₂ = l * x₂ + c)
    (hy₃eq : y₃ = l * x₃ + c)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) (hy₃ : y₃ ≠ 0) (hc : c ≠ 0) :
    nosLineC₃ W (-l / c) * (-x₁ / y₁ + -x₂ / y₂ + -x₃ / y₃) +
      nosLineC₂ W (-l / c) (-1 / c) = 0 := by
  have hD : (l * x₁ + c) * (l * x₂ + c) * (l * x₃ + c) =
      c ^ 3 - W.a₂ * l * c ^ 2 + W.a₄ * l ^ 2 * c - W.a₆ * l ^ 3 := by
    dsimp [nosLineQ₂, nosLineQ₁, nosLineQ₀] at hs₁ hs₂ hs₃
    linear_combination -l * c ^ 2 * hs₁ + l ^ 2 * c * hs₂ - l ^ 3 * hs₃
  have hN :
      x₁ * (l * x₂ + c) * (l * x₃ + c) +
          x₂ * (l * x₁ + c) * (l * x₃ + c) +
          x₃ * (l * x₁ + c) * (l * x₂ + c) =
        -W.a₁ * l * c ^ 2 - W.a₂ * c ^ 2 + W.a₃ * l ^ 2 * c +
          2 * W.a₄ * l * c - 3 * W.a₆ * l ^ 2 := by
    dsimp [nosLineQ₂, nosLineQ₁, nosLineQ₀] at hs₁ hs₂ hs₃
    linear_combination -c ^ 2 * hs₁ + 2 * l * c * hs₂ - 3 * l ^ 2 * hs₃
  have hC₃ : nosLineC₃ W (-l / c) =
      ((l * x₁ + c) * (l * x₂ + c) * (l * x₃ + c)) / c ^ 3 := by
    rw [hD]
    dsimp [nosLineC₃]
    field_simp [hc]
    ring
  have hC₂ : nosLineC₂ W (-l / c) (-1 / c) =
      (x₁ * (l * x₂ + c) * (l * x₃ + c) +
          x₂ * (l * x₁ + c) * (l * x₃ + c) +
          x₃ * (l * x₁ + c) * (l * x₂ + c)) / c ^ 3 := by
    rw [hN]
    dsimp [nosLineC₂]
    field_simp [hc]
    ring
  rw [hy₁eq] at hy₁ ⊢
  rw [hy₂eq] at hy₂ ⊢
  rw [hy₃eq] at hy₃ ⊢
  rw [hC₃, hC₂]
  field_simp [hy₁, hy₂, hy₃, hc]
  ring

lemma nos_secant_vieta {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ x₂ x₃ y₁ y₂ y₃ l c : K}
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂) (hx : x₁ ≠ x₂)
    (hy₁eq : y₁ = l * x₁ + c) (hy₂eq : y₂ = l * x₂ + c)
    (hy₃eq : y₃ = l * x₃ + c) (hx₃ : x₃ = nosLineQ₂ W l - x₁ - x₂)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) (hy₃ : y₃ ≠ 0) (hc : c ≠ 0) :
    nosLineC₃ W (-l / c) * (-x₁ / y₁ + -x₂ / y₂ + -x₃ / y₃) +
      nosLineC₂ W (-l / c) (-1 / c) = 0 := by
  have hr₁ := nos_line_root W h₁ hy₁eq
  have hr₂ := nos_line_root W h₂ hy₂eq
  obtain ⟨hs₂, hs₃⟩ := nos_secant_symmetric W hr₁ hr₂ hx
  apply nos_transformed_vieta W (x₁ := x₁) (x₂ := x₂) (x₃ := x₃)
    (y₁ := y₁) (y₂ := y₂) (y₃ := y₃) (l := l) (c := c)
  · rw [hx₃]
    ring
  · simpa only [hx₃] using hs₂
  · simpa only [hx₃] using hs₃
  · exact hy₁eq
  · exact hy₂eq
  · exact hy₃eq
  · exact hy₁
  · exact hy₂
  · exact hy₃
  · exact hc

lemma nos_tangent_symmetric {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x l c : K}
    (hroot : -x ^ 3 + nosLineQ₂ W l * x ^ 2 + nosLineQ₁ W l c * x +
      nosLineQ₀ W c = 0)
    (hderiv : -3 * x ^ 2 + 2 * nosLineQ₂ W l * x + nosLineQ₁ W l c = 0) :
    let x₃ := nosLineQ₂ W l - 2 * x
    nosLineQ₁ W l c = -(x * x + x * x₃ + x * x₃) ∧
      nosLineQ₀ W c = x * x * x₃ := by
  dsimp
  constructor
  · linear_combination hderiv
  · linear_combination hroot - x * hderiv

lemma nos_tangent_derivative_of_mul {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x y l c : K} (hc : c = y - l * x)
    (hl : l * (2 * y + W.a₁ * x + W.a₃) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) :
    -3 * x ^ 2 + 2 * nosLineQ₂ W l * x + nosLineQ₁ W l c = 0 := by
  rw [hc]
  dsimp [nosLineQ₂, nosLineQ₁]
  linear_combination hl

lemma nos_tangent_vieta {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x x₃ y y₃ l c : K} (h : WeierstrassCurve.Affine.Equation W x y)
    (hyEq : y = l * x + c) (hy₃eq : y₃ = l * x₃ + c)
    (hx₃ : x₃ = nosLineQ₂ W l - 2 * x)
    (hderiv : -3 * x ^ 2 + 2 * nosLineQ₂ W l * x + nosLineQ₁ W l c = 0)
    (hy : y ≠ 0) (hy₃ : y₃ ≠ 0) (hc : c ≠ 0) :
    nosLineC₃ W (-l / c) * (-x / y + -x / y + -x₃ / y₃) +
      nosLineC₂ W (-l / c) (-1 / c) = 0 := by
  have hr := nos_line_root W h hyEq
  obtain ⟨hs₂, hs₃⟩ := nos_tangent_symmetric W hr hderiv
  apply nos_transformed_vieta W (x₁ := x) (x₂ := x) (x₃ := x₃)
    (y₁ := y) (y₂ := y) (y₃ := y₃) (l := l) (c := c)
  · rw [hx₃]
    ring
  · simpa only [hx₃] using hs₂
  · simpa only [hx₃] using hs₃
  · exact hyEq
  · exact hyEq
  · exact hy₃eq
  · exact hy
  · exact hy
  · exact hy₃
  · exact hc

lemma nos_transformed_line {K : Type*} [Field K]
    {x y l c : K} (hy : y ≠ 0) (hc : c ≠ 0) (hline : y = l * x + c) :
    -1 / y = (-l / c) * (-x / y) + -1 / c := by
  field_simp [hy, hc]
  linear_combination hline

lemma nos_line_slope {K : Type*} [Field K]
    {z₁ z₂ w₁ w₂ a b : K} (hz : z₁ ≠ z₂)
    (h₁ : w₁ = a * z₁ + b) (h₂ : w₂ = a * z₂ + b) :
    a = (w₂ - w₁) / (z₂ - z₁) ∧ b = w₁ - a * z₁ := by
  have hdz : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr hz.symm
  constructor
  · apply (eq_div_iff hdz).mpr
    linear_combination h₁ - h₂
  · linear_combination -h₁

lemma nos_tangent_transform {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x y z w l c : K} (h : WeierstrassCurve.Affine.Equation W x y) (hy : y ≠ 0)
    (hden : 2 * y + W.a₁ * x + W.a₃ ≠ 0)
    (hz : z = -x / y) (hw : w = -1 / y)
    (hl : l = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) /
      (2 * y + W.a₁ * x + W.a₃))
    (hc : c = y - l * x) (hU : nosChordU W z w w ≠ 0) :
    c ≠ 0 ∧ -l / c = nosChordV W z z w / nosChordU W z w w ∧
      -1 / c = w - (nosChordV W z z w / nosChordU W z w w) * z := by
  have hlmul : l * (2 * y + W.a₁ * x + W.a₃) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hl]
    exact div_mul_cancel₀ _ hden
  have hcurve := (WeierstrassCurve.Affine.equation_iff (W := W) x y).mp h
  have hUy : nosChordU W z w w * y ^ 2 = x ^ 3 - W.a₄ * x - 2 * W.a₆ + W.a₃ * y := by
    rw [hz, hw]
    dsimp [nosChordU]
    field_simp [hy]
    linear_combination hcurve
  have hVy : nosChordV W z z w * y ^ 2 =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hz, hw]
    dsimp [nosChordV]
    field_simp [hy]
    ring
  have hcD : c * (2 * y + W.a₁ * x + W.a₃) = -(nosChordU W z w w * y ^ 2) := by
    rw [hc]
    linear_combination 2 * hcurve + hUy - x * hlmul
  have hc0 : c ≠ 0 := by
    intro hczero
    rw [hczero, zero_mul] at hcD
    have hzero : nosChordU W z w w * y ^ 2 = 0 := by
      linear_combination hcD
    exact (mul_ne_zero hU (pow_ne_zero 2 hy)) hzero
  refine ⟨hc0, ?_, ?_⟩
  · apply (div_eq_div_iff hc0 hU).mpr
    apply mul_right_cancel₀ hden
    linear_combination -nosChordU W z w w * hlmul - nosChordV W z z w * hcD +
      nosChordU W z w w * hVy
  · have hline : y = l * x + c := by
      rw [hc]
      ring
    have htrans := nos_transformed_line hy hc0 hline
    have ha : -l / c = nosChordV W z z w / nosChordU W z w w := by
      apply (div_eq_div_iff hc0 hU).mpr
      apply mul_right_cancel₀ hden
      linear_combination -nosChordU W z w w * hlmul - nosChordV W z z w * hcD +
        nosChordU W z w w * hVy
    rw [← ha, hw, hz]
    linear_combination -htrans

lemma nos_chord_z_ne {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ x₂ y₁ y₂ z₁ z₂ w₁ w₂ : K} (hx : x₁ ≠ x₂)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hz₁ : z₁ = -x₁ / y₁) (hz₂ : z₂ = -x₂ / y₂)
    (hw₁ : w₁ = -1 / y₁) (hw₂ : w₂ = -1 / y₂)
    (h₁ : nosLocalEquation W z₁ w₁) (h₂ : nosLocalEquation W z₂ w₂)
    (hU : nosChordU W z₁ w₁ w₂ ≠ 0) : z₁ ≠ z₂ := by
  intro hz
  have hid := nos_chord_identity W h₁ h₂
  have hzsub : z₂ - z₁ = 0 := sub_eq_zero.mpr hz.symm
  rw [hzsub, zero_mul] at hid
  have hwsub : w₂ - w₁ = 0 := (mul_eq_zero.mp hid).resolve_right hU
  have hw : w₁ = w₂ := (sub_eq_zero.mp hwsub).symm
  apply hx
  rw [hz₁, hz₂] at hz
  rw [hw₁, hw₂] at hw
  field_simp [hy₁, hy₂] at hz hw
  have hyEq : y₁ = y₂ := by
    linear_combination hw
  rw [hyEq] at hz
  apply mul_right_cancel₀ hy₂
  simpa only [neg_inj, mul_comm] using hz

lemma nos_line_intercept_ne {K : Type*} [Field K]
    {x₁ x₂ y₁ y₂ l c : K} (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hy₁eq : y₁ = l * x₁ + c) (hy₂eq : y₂ = l * x₂ + c)
    (hz : -x₁ / y₁ ≠ -x₂ / y₂) : c ≠ 0 := by
  intro hc
  apply hz
  apply (div_eq_div_iff hy₁ hy₂).mpr
  rw [hy₁eq, hy₂eq, hc]
  ring

lemma nos_transformed_leading {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ x₂ x₃ y₁ y₂ y₃ l c : K}
    (hs₁ : nosLineQ₂ W l = x₁ + x₂ + x₃)
    (hs₂ : nosLineQ₁ W l c = -(x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hs₃ : nosLineQ₀ W c = x₁ * x₂ * x₃)
    (hy₁eq : y₁ = l * x₁ + c) (hy₂eq : y₂ = l * x₂ + c)
    (hy₃eq : y₃ = l * x₃ + c) (hc : c ≠ 0) :
    nosLineC₃ W (-l / c) = y₁ * y₂ * y₃ / c ^ 3 := by
  have hD : (l * x₁ + c) * (l * x₂ + c) * (l * x₃ + c) =
      c ^ 3 - W.a₂ * l * c ^ 2 + W.a₄ * l ^ 2 * c - W.a₆ * l ^ 3 := by
    dsimp [nosLineQ₂, nosLineQ₁, nosLineQ₀] at hs₁ hs₂ hs₃
    linear_combination -l * c ^ 2 * hs₁ + l ^ 2 * c * hs₂ - l ^ 3 * hs₃
  rw [hy₁eq, hy₂eq, hy₃eq, hD]
  dsimp [nosLineC₃]
  field_simp [hc]
  ring

lemma nos_chord_U_unit {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z₁ z₂ w₁ w₂ : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hz₁ : A.valuation z₁ < 1) (hz₂ : A.valuation z₂ ≤ A.valuation z₁)
    (hw₁ : A.valuation w₁ = A.valuation z₁ ^ 3)
    (hw₂ : A.valuation w₂ = A.valuation z₂ ^ 3) :
    A.valuation (nosChordU W z₁ w₁ w₂) = 1 := by
  let v := A.valuation
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₂v : v W.a₂ ≤ 1 := (A.valuation_le_one_iff W.a₂).mpr ha₂
  have ha₃v : v W.a₃ ≤ 1 := (A.valuation_le_one_iff W.a₃).mpr ha₃
  have ha₄v : v W.a₄ ≤ 1 := (A.valuation_le_one_iff W.a₄).mpr ha₄
  have ha₆v : v W.a₆ ≤ 1 := (A.valuation_le_one_iff W.a₆).mpr ha₆
  have hz₂' : v z₂ < 1 := hz₂.trans_lt hz₁
  have hw₁' : v w₁ < 1 := by
    rw [hw₁]
    exact pow_lt_one₀ zero_le hz₁ (by decide)
  have hw₂' : v w₂ < 1 := by
    rw [hw₂]
    exact pow_lt_one₀ zero_le hz₂' (by decide)
  have hwadd : v (w₂ + w₁) < 1 := v.map_add_lt hw₂' hw₁'
  have hwquad : v (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2) < 1 := by
    apply v.map_add_lt
    · apply v.map_add_lt <;> simp only [v, Valuation.map_mul, Valuation.map_pow]
      · exact pow_lt_one₀ zero_le hw₂' (by decide)
      · exact (mul_le_of_le_one_right zero_le hw₁'.le).trans_lt hw₂'
    · simp only [v, Valuation.map_pow]
      exact pow_lt_one₀ zero_le hw₁' (by decide)
  have hsmall : v (W.a₁ * z₁ + W.a₂ * z₁ ^ 2 + W.a₃ * (w₂ + w₁) +
      W.a₄ * z₁ * (w₂ + w₁) + W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2)) < 1 := by
    apply v.map_add_lt
    · apply v.map_add_lt
      · apply v.map_add_lt
        · apply v.map_add_lt
          · simp only [v, Valuation.map_mul]
            exact (mul_le_of_le_one_left zero_le ha₁v).trans_lt hz₁
          · simp only [v, Valuation.map_mul, Valuation.map_pow]
            exact (mul_le_of_le_one_left zero_le ha₂v).trans_lt
              (pow_lt_one₀ zero_le hz₁ (by decide))
        · simp only [v, Valuation.map_mul]
          exact (mul_le_of_le_one_left zero_le ha₃v).trans_lt hwadd
      · simp only [v, Valuation.map_mul]
        apply (mul_le_of_le_one_left zero_le ?_).trans_lt hwadd
        exact (mul_le_of_le_one_left zero_le ha₄v).trans hz₁.le
    · simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_left zero_le ha₆v).trans_lt hwquad
  rw [show nosChordU W z₁ w₁ w₂ =
      1 - (W.a₁ * z₁ + W.a₂ * z₁ ^ 2 + W.a₃ * (w₂ + w₁) +
        W.a₄ * z₁ * (w₂ + w₁) +
          W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2)) by
      simp only [nosChordU]
      ring]
  exact v.map_one_sub_of_lt hsmall

lemma nos_chord_V_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z₁ z₂ w₂ : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₄ : W.a₄ ∈ A)
    (hz₁ : A.valuation z₁ < 1) (hz₂ : A.valuation z₂ ≤ A.valuation z₁)
    (hw₂ : A.valuation w₂ = A.valuation z₂ ^ 3) :
    A.valuation (nosChordV W z₁ z₂ w₂) ≤ A.valuation z₁ ^ 2 := by
  let v := A.valuation
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₂v : v W.a₂ ≤ 1 := (A.valuation_le_one_iff W.a₂).mpr ha₂
  have ha₄v : v W.a₄ ≤ 1 := (A.valuation_le_one_iff W.a₄).mpr ha₄
  have hw₂b : v w₂ ≤ v z₁ ^ 2 := by
    rw [hw₂]
    exact (pow_le_pow_left₀ zero_le hz₂ 3).trans
      (pow_right_anti₀ zero_le hz₁.le (by decide : 2 ≤ 3))
  have hw₂one : v w₂ ≤ 1 := hw₂b.trans (pow_le_one₀ zero_le hz₁.le)
  have hzsum : v (z₂ + z₁) ≤ v z₁ :=
    (v.map_add z₂ z₁).trans (max_le hz₂ le_rfl)
  have h₁ : v (z₂ ^ 2) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_pow]
    exact pow_le_pow_left₀ zero_le hz₂ 2
  have h₂ : v (z₂ * z₁) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_mul, pow_two]
    exact mul_le_mul_of_nonneg_right hz₂ zero_le
  have h₃ : v (z₁ ^ 2) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_pow]
    exact le_rfl
  have h₄ : v (W.a₁ * w₂) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₁v).trans hw₂b
  have h₅ : v (W.a₂ * (z₂ + z₁) * w₂) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_mul]
    apply (mul_le_of_le_one_left zero_le ?_).trans hw₂b
    exact (mul_le_of_le_one_left zero_le ha₂v).trans (hzsum.trans hz₁.le)
  have h₆ : v (W.a₄ * w₂ ^ 2) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_mul, Valuation.map_pow]
    exact (mul_le_of_le_one_left zero_le ha₄v).trans
      ((sq_le zero_le hw₂one).trans hw₂b)
  have hadd {a b : K} (ha : v a ≤ v z₁ ^ 2) (hb : v b ≤ v z₁ ^ 2) :
      v (a + b) ≤ v z₁ ^ 2 :=
    (v.map_add a b).trans (max_le ha hb)
  exact hadd (hadd (hadd (hadd (hadd h₁ h₂) h₃) h₄) h₅) h₆

lemma nos_chord_slope_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z₁ z₂ w₁ w₂ : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hz₁ : A.valuation z₁ < 1) (hz₂ : A.valuation z₂ ≤ A.valuation z₁)
    (hw₁ : A.valuation w₁ = A.valuation z₁ ^ 3)
    (hw₂ : A.valuation w₂ = A.valuation z₂ ^ 3)
    (h₁ : nosLocalEquation W z₁ w₁) (h₂ : nosLocalEquation W z₂ w₂)
    (hz : z₁ ≠ z₂) :
    A.valuation ((w₂ - w₁) / (z₂ - z₁)) ≤ A.valuation z₁ ^ 2 := by
  let v := A.valuation
  have hU := nos_chord_U_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hz₁ hz₂ hw₁ hw₂
  have hV := nos_chord_V_bound W A ha₁ ha₂ ha₄ hz₁ hz₂ hw₂
  have hU0 : nosChordU W z₁ w₁ w₂ ≠ 0 := by
    apply v.ne_zero_iff.mp
    rw [hU]
    exact one_ne_zero
  have hdz : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr hz.symm
  have hslope : (w₂ - w₁) / (z₂ - z₁) =
      nosChordV W z₁ z₂ w₂ / nosChordU W z₁ w₁ w₂ := by
    field_simp [hdz, hU0]
    simpa only [mul_comm] using nos_chord_identity W h₁ h₂
  rw [hslope, v.map_div, hU, div_one]
  exact hV

lemma nos_tangent_U_unit {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z w : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hz : A.valuation z < 1) (hw : A.valuation w = A.valuation z ^ 3) :
    A.valuation (nosChordU W z w w) = 1 :=
  nos_chord_U_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hz le_rfl hw hw

lemma nos_tangent_V_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z w : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₄ : W.a₄ ∈ A)
    (hz : A.valuation z < 1) (hw : A.valuation w = A.valuation z ^ 3) :
    A.valuation (nosChordV W z z w) ≤ A.valuation z ^ 2 :=
  nos_chord_V_bound W A ha₁ ha₂ ha₄ hz le_rfl hw

lemma nos_tangent_slope_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z w : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hz : A.valuation z < 1) (hw : A.valuation w = A.valuation z ^ 3) :
    A.valuation (nosChordV W z z w / nosChordU W z w w) ≤ A.valuation z ^ 2 := by
  rw [A.valuation.map_div, nos_tangent_U_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hz hw,
    div_one]
  exact nos_tangent_V_bound W A ha₁ ha₂ ha₄ hz hw

lemma nos_line_coefficients_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {a b : K} {s : A.ValueGroup}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hs : s < 1) (ha : A.valuation a ≤ s ^ 2)
    (hb : A.valuation b ≤ s ^ 3) :
    A.valuation (nosLineC₃ W a) = 1 ∧
      A.valuation (nosLineC₂ W a b) ≤ s ^ 2 := by
  let v := A.valuation
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₂v : v W.a₂ ≤ 1 := (A.valuation_le_one_iff W.a₂).mpr ha₂
  have ha₃v : v W.a₃ ≤ 1 := (A.valuation_le_one_iff W.a₃).mpr ha₃
  have ha₄v : v W.a₄ ≤ 1 := (A.valuation_le_one_iff W.a₄).mpr ha₄
  have ha₆v : v W.a₆ ≤ 1 := (A.valuation_le_one_iff W.a₆).mpr ha₆
  have hs₂one : s ^ 2 ≤ 1 := pow_le_one₀ zero_le hs.le
  have hs₃₂ : s ^ 3 ≤ s ^ 2 := pow_right_anti₀ zero_le hs.le (by decide)
  have haone : v a ≤ 1 := ha.trans hs₂one
  have hbone : v b ≤ 1 := hb.trans (hs₃₂.trans hs₂one)
  have haa : v (a ^ 2) ≤ v a := by
    simp only [v, Valuation.map_pow]
    exact sq_le zero_le haone
  have haaa : v (a ^ 3) ≤ v a := by
    simp only [v, Valuation.map_pow]
    exact pow_le_of_le_one zero_le haone (by decide)
  have h₂a₄v : v ((2 : K) * W.a₄) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (A.mul_mem (2 : K) W.a₄ (natCast_mem A 2) ha₄)
  have h₃a₆v : v ((3 : K) * W.a₆) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (A.mul_mem (3 : K) W.a₆ (natCast_mem A 3) ha₆)
  have halt : v a < 1 := ha.trans_lt (pow_lt_one₀ zero_le hs (by decide))
  have hc₃₂ : v (W.a₂ * a) < 1 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₂v).trans_lt (ha.trans_lt
      (pow_lt_one₀ zero_le hs (by decide)))
  have hc₃₄ : v (W.a₄ * a ^ 2) < 1 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₄v).trans_lt
      (haa.trans_lt halt)
  have hc₃₆ : v (W.a₆ * a ^ 3) < 1 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₆v).trans_lt
      (haaa.trans_lt halt)
  constructor
  · rw [show nosLineC₃ W a =
        1 + (W.a₂ * a + W.a₄ * a ^ 2 + W.a₆ * a ^ 3) by
      simp only [nosLineC₃]
      ring]
    exact v.map_one_add_of_lt (v.map_add_lt (v.map_add_lt hc₃₂ hc₃₄) hc₃₆)
  · have h₁ : v (W.a₁ * a) ≤ s ^ 2 := by
      simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_left zero_le ha₁v).trans ha
    have h₂ : v (W.a₂ * b) ≤ s ^ 2 := by
      simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_left zero_le ha₂v).trans (hb.trans hs₃₂)
    have h₃ : v (W.a₃ * a ^ 2) ≤ s ^ 2 := by
      simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_left zero_le ha₃v).trans (haa.trans ha)
    have h₄ : v (2 * W.a₄ * a * b) ≤ s ^ 2 := by
      simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_right zero_le hbone).trans
        ((mul_le_of_le_one_left zero_le h₂a₄v).trans ha)
    have h₆ : v (3 * W.a₆ * a ^ 2 * b) ≤ s ^ 2 := by
      simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_right zero_le hbone).trans
        ((mul_le_of_le_one_left zero_le h₃a₆v).trans (haa.trans ha))
    have hadd {x y : K} (hx : v x ≤ s ^ 2) (hy : v y ≤ s ^ 2) :
        v (x + y) ≤ s ^ 2 := (v.map_add x y).trans (max_le hx hy)
    exact hadd (hadd (hadd (hadd h₁ h₂) h₃) h₄) h₆

lemma nos_line_intercept_bound {K : Type*} [Field K]
    (A : ValuationSubring K) {z w a : K} {s : A.ValueGroup}
    (hz : A.valuation z = s) (hw : A.valuation w = s ^ 3)
    (ha : A.valuation a ≤ s ^ 2) :
    A.valuation (w - a * z) ≤ s ^ 3 := by
  let v := A.valuation
  apply (v.map_sub w (a * z)).trans
  apply max_le
  · exact hw.le
  · simp only [v, Valuation.map_mul, hz]
    calc
      A.valuation a * s ≤ s ^ 2 * s := mul_le_mul_of_nonneg_right ha zero_le
      _ = s ^ 3 := (pow_succ s 2).symm

lemma nos_vieta_sum_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z₁ z₂ z₃ a b : K} {s : A.ValueGroup}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hs : s < 1)
    (ha : A.valuation a ≤ s ^ 2) (hb : A.valuation b ≤ s ^ 3)
    (hvieta : nosLineC₃ W a * (z₁ + z₂ + z₃) + nosLineC₂ W a b = 0) :
    A.valuation (z₁ + z₂ + z₃) ≤ s ^ 2 := by
  let v := A.valuation
  obtain ⟨hC₃, hC₂⟩ := nos_line_coefficients_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hs ha hb
  have heq : nosLineC₃ W a * (z₁ + z₂ + z₃) = -nosLineC₂ W a b := by
    linear_combination hvieta
  have hval := congrArg v heq
  simp only [Valuation.map_mul, Valuation.map_neg] at hval
  change v (nosLineC₃ W a) = 1 at hC₃
  rw [hC₃, one_mul] at hval
  change v (z₁ + z₂ + z₃) ≤ s ^ 2
  rw [hval]
  exact hC₂

lemma nos_neg_z_formula {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x y : K} (hy : y ≠ 0) (hneg : WeierstrassCurve.Affine.negY W x y ≠ 0) :
    -x / WeierstrassCurve.Affine.negY W x y =
      -(-x / y) / (1 - W.a₁ * (-x / y) - W.a₃ * (-1 / y)) := by
  simp only [WeierstrassCurve.Affine.negY] at hneg ⊢
  have hpos : x * W.a₁ + y + W.a₃ ≠ 0 := by
    intro h
    apply hneg
    linear_combination -h
  field_simp [hy, hneg, hpos]
  rw [show -y - x * W.a₁ - W.a₃ = -(x * W.a₁ + y + W.a₃) by ring,
    show y - -(x * W.a₁) - -W.a₃ = x * W.a₁ + y + W.a₃ by ring, div_neg]
  ring

lemma nos_neg_parameter {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z w : K}
    (ha₁ : W.a₁ ∈ A) (ha₃ : W.a₃ ∈ A)
    (hz : A.valuation z < 1) (hz0 : z ≠ 0)
    (hw : A.valuation w = A.valuation z ^ 3) :
    let d := 1 - W.a₁ * z - W.a₃ * w
    A.valuation d = 1 ∧ A.valuation (-z / d + z) < A.valuation z ∧
      A.valuation (-z / d) = A.valuation z := by
  let v := A.valuation
  let d := 1 - W.a₁ * z - W.a₃ * w
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₃v : v W.a₃ ≤ 1 := (A.valuation_le_one_iff W.a₃).mpr ha₃
  have hw' : v w < 1 := by
    rw [hw]
    exact pow_lt_one₀ zero_le hz (by decide)
  have ha₁z : v (W.a₁ * z) < 1 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₁v).trans_lt hz
  have ha₃w : v (W.a₃ * w) < 1 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₃v).trans_lt hw'
  have ht : v (W.a₁ * z + W.a₃ * w) < 1 := v.map_add_lt ha₁z ha₃w
  have hd : v d = 1 := by
    change v (1 - W.a₁ * z - W.a₃ * w) = 1
    rw [show 1 - W.a₁ * z - W.a₃ * w = 1 - (W.a₁ * z + W.a₃ * w) by ring]
    exact v.map_one_sub_of_lt ht
  have hd0 : d ≠ 0 := by
    apply v.ne_zero_iff.mp
    rw [hd]
    exact one_ne_zero
  have hdsub : v (d - 1) < 1 := by
    change v ((1 - W.a₁ * z - W.a₃ * w) - 1) < 1
    rw [show (1 - W.a₁ * z - W.a₃ * w) - 1 =
      -(W.a₁ * z + W.a₃ * w) by ring, v.map_neg]
    exact ht
  refine ⟨hd, ?_, ?_⟩
  · rw [show -z / d + z = z * (d - 1) / d by field_simp [hd0]; ring,
      v.map_div, v.map_mul, hd, div_one]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hdsub (v.pos_iff.mpr hz0)
  · change v (-z / d) = v z
    rw [v.map_div, v.map_neg, hd, div_one]

lemma nos_y_mem_of_x_mem {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x y : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hx : x ∈ A)
    (hxy : WeierstrassCurve.Affine.Equation W x y) : y ∈ A := by
  let a₁ : A := ⟨W.a₁, ha₁⟩
  let a₂ : A := ⟨W.a₂, ha₂⟩
  let a₃ : A := ⟨W.a₃, ha₃⟩
  let a₄ : A := ⟨W.a₄, ha₄⟩
  let a₆ : A := ⟨W.a₆, ha₆⟩
  let xA : A := ⟨x, hx⟩
  let p : Polynomial A := Polynomial.X ^ 2 + Polynomial.C (a₁ * xA + a₃) * Polynomial.X -
    Polynomial.C (xA ^ 3 + a₂ * xA ^ 2 + a₄ * xA + a₆)
  have hp : p.Monic := by
    dsimp [p]
    monicity!
  have hpy : Polynomial.aeval y p = 0 := by
    rw [WeierstrassCurve.Affine.equation_iff (W := W) x y] at hxy
    simp only [p, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C]
    change y ^ 2 + (W.a₁ * x + W.a₃) * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0
    linear_combination hxy
  have hy : IsIntegral A y := ⟨p, hp, hpy⟩
  obtain ⟨yA, hyA⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  rw [← hyA]
  exact yA.property

lemma nos_x_mem_of_y_mem {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x y : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hy : y ∈ A)
    (hxy : WeierstrassCurve.Affine.Equation W x y) : x ∈ A := by
  let a₁ : A := ⟨W.a₁, ha₁⟩
  let a₂ : A := ⟨W.a₂, ha₂⟩
  let a₃ : A := ⟨W.a₃, ha₃⟩
  let a₄ : A := ⟨W.a₄, ha₄⟩
  let a₆ : A := ⟨W.a₆, ha₆⟩
  let yA : A := ⟨y, hy⟩
  let p : Polynomial A := Polynomial.X ^ 3 + Polynomial.C a₂ * Polynomial.X ^ 2 +
    Polynomial.C (a₄ - a₁ * yA) * Polynomial.X +
      Polynomial.C (a₆ - yA ^ 2 - a₃ * yA)
  have hp : p.Monic := by
    dsimp [p]
    monicity!
  have hpx : Polynomial.aeval x p = 0 := by
    rw [WeierstrassCurve.Affine.equation_iff (W := W) x y] at hxy
    simp only [p, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C]
    change x ^ 3 + W.a₂ * x ^ 2 + (W.a₄ - W.a₁ * y) * x +
      (W.a₆ - y ^ 2 - W.a₃ * y) = 0
    linear_combination -hxy
  have hx : IsIntegral A x := ⟨p, hp, hpx⟩
  obtain ⟨xA, hxA⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  rw [← hxA]
  exact xA.property

lemma nos_cubic_dominant {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x : K} (ha₂ : W.a₂ ∈ A) (ha₄ : W.a₄ ∈ A)
    (ha₆ : W.a₆ ∈ A) (hx : x ∉ A) :
    A.valuation (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) =
      A.valuation (x ^ 3) := by
  let v := A.valuation
  have hxv : 1 < v x := by
    rw [← not_le]
    exact fun h ↦ hx ((A.valuation_le_one_iff x).mp h)
  have ha₂v : v W.a₂ ≤ 1 := (A.valuation_le_one_iff W.a₂).mpr ha₂
  have ha₄v : v W.a₄ ≤ 1 := (A.valuation_le_one_iff W.a₄).mpr ha₄
  have ha₆v : v W.a₆ ≤ 1 := (A.valuation_le_one_iff W.a₆).mpr ha₆
  have h₂ : v (W.a₂ * x ^ 2) < v (x ^ 3) := by
    simp only [v, Valuation.map_mul, Valuation.map_pow]
    exact mul_lt_of_le_one_of_lt ha₂v (pow_lt_pow_right₀ hxv (by decide))
  have h₄ : v (W.a₄ * x) < v (x ^ 3) := by
    simp only [v, Valuation.map_mul, Valuation.map_pow]
    exact mul_lt_of_le_one_of_lt ha₄v (by
      simpa only [pow_one] using pow_lt_pow_right₀ hxv (by decide : 1 < 3))
  have h₆ : v W.a₆ < v (x ^ 3) := by
    simp only [v, Valuation.map_pow]
    exact ha₆v.trans_lt (by
      simpa only [pow_zero] using pow_lt_pow_right₀ hxv (by decide : 0 < 3))
  have h₃₂ : v (x ^ 3 + W.a₂ * x ^ 2) = v (x ^ 3) :=
    v.map_add_eq_of_lt_left h₂
  have h₃₂₄ : v (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x) = v (x ^ 3) := by
    rw [v.map_add_eq_of_lt_left]
    · exact h₃₂
    · rwa [h₃₂]
  rw [v.map_add_eq_of_lt_left]
  · exact h₃₂₄
  · rwa [h₃₂₄]

lemma nos_nonintegral_valuations {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x y : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hx : x ∉ A)
    (hxy : WeierstrassCurve.Affine.Equation W x y) :
    y ∉ A ∧ A.valuation x < A.valuation y ∧
      A.valuation (y ^ 2) = A.valuation (x ^ 3) := by
  let v := A.valuation
  have hy : y ∉ A := fun hy ↦ hx (nos_x_mem_of_y_mem W A ha₁ ha₂ ha₃ ha₄ ha₆ hy hxy)
  have hxv : 1 < v x := by
    rw [← not_le]
    exact fun h ↦ hx ((A.valuation_le_one_iff x).mp h)
  have hyv : 1 < v y := by
    rw [← not_le]
    exact fun h ↦ hy ((A.valuation_le_one_iff y).mp h)
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₃v : v W.a₃ ≤ 1 := (A.valuation_le_one_iff W.a₃).mpr ha₃
  have hrhs := nos_cubic_dominant W A ha₂ ha₄ ha₆ hx
  have heq := congrArg v ((WeierstrassCurve.Affine.equation_iff (W := W) x y).mp hxy)
  have hvxy : v x < v y := by
    by_contra h
    have hyx : v y ≤ v x := le_of_not_gt h
    have hy2 : v (y ^ 2) < v (x ^ 3) := by
      simp only [v, Valuation.map_pow]
      exact (pow_le_pow_left₀ zero_le hyx 2).trans_lt
        (pow_lt_pow_right₀ hxv (by decide : 2 < 3))
    have ha₁xy : v (W.a₁ * x * y) < v (x ^ 3) := by
      simp only [v, Valuation.map_mul, Valuation.map_pow]
      calc
        v W.a₁ * v x * v y ≤ 1 * v x * v y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha₁v zero_le) zero_le
        _ = v x * v y := by rw [one_mul]
        _ ≤ v x * v x := mul_le_mul_of_nonneg_left hyx zero_le
        _ = (v x) ^ 2 := (pow_two _).symm
        _ < (v x) ^ 3 := pow_lt_pow_right₀ hxv (by decide)
    have ha₃y : v (W.a₃ * y) < v (x ^ 3) := by
      simp only [v, Valuation.map_mul, Valuation.map_pow]
      calc
        v W.a₃ * v y ≤ 1 * v y := mul_le_mul_of_nonneg_right ha₃v zero_le
        _ = v y := one_mul _
        _ ≤ v x := hyx
        _ = (v x) ^ 1 := (pow_one _).symm
        _ < (v x) ^ 3 := pow_lt_pow_right₀ hxv (by decide)
    have hlhs : v (y ^ 2 + W.a₁ * x * y + W.a₃ * y) < v (x ^ 3) :=
      v.map_add_lt (v.map_add_lt hy2 ha₁xy) ha₃y
    rw [hrhs] at heq
    exact (ne_of_lt hlhs) heq
  have ha₁xy : v (W.a₁ * x * y) < v (y ^ 2) := by
    simp only [v, Valuation.map_mul, Valuation.map_pow]
    calc
      v W.a₁ * v x * v y ≤ 1 * v x * v y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha₁v zero_le) zero_le
      _ = v x * v y := by rw [one_mul]
      _ < v y * v y := mul_lt_mul_of_pos_right hvxy (zero_lt_one.trans hyv)
      _ = (v y) ^ 2 := (pow_two _).symm
  have ha₃y : v (W.a₃ * y) < v (y ^ 2) := by
    simp only [v, Valuation.map_mul, Valuation.map_pow]
    calc
      v W.a₃ * v y ≤ 1 * v y := mul_le_mul_of_nonneg_right ha₃v zero_le
      _ = v y := one_mul _
      _ < v y * v y := lt_mul_self hyv
      _ = (v y) ^ 2 := (pow_two _).symm
  have hlhs : v (y ^ 2 + W.a₁ * x * y + W.a₃ * y) = v (y ^ 2) := by
    rw [v.map_add_eq_of_lt_left]
    · exact v.map_add_eq_of_lt_left ha₁xy
    · rwa [v.map_add_eq_of_lt_left ha₁xy]
  refine ⟨hy, hvxy, ?_⟩
  rw [← hlhs, heq, hrhs]

lemma nos_local_coordinate_valuations {K : Type*} [Field K]
    (W : WeierstrassCurve K) (A : ValuationSubring K) {x y : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hx : x ∉ A)
    (hxy : WeierstrassCurve.Affine.Equation W x y) :
    y ≠ 0 ∧ -x / y ∈ A.nonunits ∧
      A.valuation (-1 / y) = A.valuation (-x / y) ^ 3 := by
  let v := A.valuation
  obtain ⟨hy, hvxy, hpow⟩ := nos_nonintegral_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx hxy
  have hy0 : y ≠ 0 := fun h ↦ hy (h ▸ A.zero_mem)
  have hvy0 : v y ≠ 0 := v.ne_zero_iff.mpr hy0
  refine ⟨hy0, ?_, ?_⟩
  · rw [A.mem_nonunits_iff]
    simp only [Valuation.map_div, Valuation.map_neg]
    exact (div_lt_one₀ (v.pos_iff.mpr hy0)).mpr hvxy
  · simp only [Valuation.map_div, Valuation.map_neg, Valuation.map_one]
    rw [div_pow]
    have hpow' : (v y) ^ 2 = (v x) ^ 3 := by
      simpa only [v, Valuation.map_pow] using hpow
    rw [← hpow']
    apply (div_eq_div_iff hvy0 (pow_ne_zero 3 hvy0)).mpr
    simp only [one_mul, pow_succ]

lemma nos_finish_add {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x₃ y₃ z₁ z₂ z₃ a b : K} {s : A.ValueGroup}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (h₃ : WeierstrassCurve.Affine.Equation W x₃ y₃) (hy₃ : y₃ ≠ 0)
    (hz₃ : z₃ = -x₃ / y₃) (hline₃ : -1 / y₃ = a * z₃ + b)
    (hs0 : 0 < s) (hs : s < 1) (hz₁ : A.valuation z₁ = s)
    (hz₂ : A.valuation z₂ ≤ s) (ha : A.valuation a ≤ s ^ 2)
    (hb : A.valuation b ≤ s ^ 3)
    (hsum : A.valuation (z₁ + z₂ + z₃) ≤ s ^ 2) :
    x₃ ∉ A ∧ A.valuation
      (-x₃ / WeierstrassCurve.Affine.negY W x₃ y₃ - z₁ - z₂) < s := by
  let v := A.valuation
  have hs₂s : s ^ 2 < s := pow_lt_self_of_lt_one₀ hs0 hs (by decide)
  have hz₃le : v z₃ ≤ s := by
    rw [show z₃ = (z₁ + z₂ + z₃) - z₁ - z₂ by ring]
    exact (v.map_sub _ _).trans (max_le
      ((v.map_sub _ _).trans (max_le (hsum.trans hs₂s.le) hz₁.le)) hz₂)
  have haw : v (a * z₃) ≤ s ^ 3 := by
    simp only [v, Valuation.map_mul]
    calc
      v a * v z₃ ≤ s ^ 2 * s :=
        mul_le_mul ha hz₃le zero_le (pow_nonneg zero_le 2)
      _ = s ^ 3 := (pow_succ s 2).symm
  have hw₃ : v (-1 / y₃) ≤ s ^ 3 := by
    rw [hline₃]
    exact (v.map_add _ _).trans (max_le haw hb)
  have hw₃lt : v (-1 / y₃) < 1 :=
    hw₃.trans_lt (pow_lt_one₀ zero_le hs (by decide))
  have hy₃not : y₃ ∉ A := by
    intro hyA
    have hyv : v y₃ ≤ 1 := (A.valuation_le_one_iff y₃).mpr hyA
    have hyv0 : 0 < v y₃ := v.pos_iff.mpr hy₃
    have hone : 1 ≤ v (-1 / y₃) := by
      simp only [v, Valuation.map_div, Valuation.map_neg, Valuation.map_one]
      simpa only [one_div] using (one_le_inv₀ hyv0).mpr hyv
    exact (not_lt_of_ge hone) hw₃lt
  have hx₃not : x₃ ∉ A := fun hxA ↦ hy₃not
    (nos_y_mem_of_x_mem W A ha₁ ha₂ ha₃ ha₄ ha₆ hxA h₃)
  refine ⟨hx₃not, ?_⟩
  obtain ⟨_, hz₃nonunit, hwz₃⟩ :=
    nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx₃not h₃
  have hz₃lt : v z₃ < 1 := by
    rw [hz₃]
    exact (A.mem_nonunits_iff.mpr hz₃nonunit)
  have hx₃0 : x₃ ≠ 0 := fun hx ↦ hx₃not (hx ▸ A.zero_mem)
  have hz₃0 : z₃ ≠ 0 := by
    rw [hz₃]
    exact div_ne_zero (neg_ne_zero.mpr hx₃0) hy₃
  have hneg : WeierstrassCurve.Affine.negY W x₃ y₃ ≠ 0 := by
    intro hzero
    have hyneg : WeierstrassCurve.Affine.negY W x₃ y₃ ∈ A := hzero ▸ A.zero_mem
    exact hx₃not (nos_x_mem_of_y_mem W A ha₁ ha₂ ha₃ ha₄ ha₆ hyneg
      ((WeierstrassCurve.Affine.equation_neg x₃ y₃).mpr h₃))
  have hform := nos_neg_z_formula W hy₃ hneg
  rw [← hz₃] at hwz₃
  obtain ⟨_, hnegerr, _⟩ := nos_neg_parameter W A ha₁ ha₃ hz₃lt hz₃0 hwz₃
  rw [hform, ← hz₃]
  rw [show -z₃ / (1 - W.a₁ * z₃ - W.a₃ * (-1 / y₃)) - z₁ - z₂ =
      (-z₃ / (1 - W.a₁ * z₃ - W.a₃ * (-1 / y₃)) + z₃) -
        (z₁ + z₂ + z₃) by ring]
  exact v.map_sub_lt (hnegerr.trans_le hz₃le) (hsum.trans_lt hs₂s)

lemma nos_secant_add {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) (A : ValuationSubring K) {x₁ x₂ y₁ y₂ : K}
    {s : A.ValueGroup} (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A) (hx : x₁ ≠ x₂) (hs0 : 0 < s)
    (hz₁val : A.valuation (-x₁ / y₁) = s) (hz₂val : A.valuation (-x₂ / y₂) ≤ s) :
    let l := WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂
    let x₃ := WeierstrassCurve.Affine.addX W x₁ x₂ l
    let y₃ := WeierstrassCurve.Affine.negAddY W x₁ x₂ y₁ l
    x₃ ∉ A ∧ A.valuation
      (-x₃ / WeierstrassCurve.Affine.negY W x₃ y₃ - (-x₁ / y₁) - (-x₂ / y₂)) < s := by
  let v := A.valuation
  let z₁ := -x₁ / y₁
  let z₂ := -x₂ / y₂
  let w₁ := -1 / y₁
  let w₂ := -1 / y₂
  let l := WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂
  let c := y₁ - l * x₁
  let a := -l / c
  let b := -1 / c
  let x₃ := WeierstrassCurve.Affine.addX W x₁ x₂ l
  let y₃ := WeierstrassCurve.Affine.negAddY W x₁ x₂ y₁ l
  let z₃ := -x₃ / y₃
  dsimp only
  change x₃ ∉ A ∧ v (-x₃ / WeierstrassCurve.Affine.negY W x₃ y₃ - z₁ - z₂) < s
  obtain ⟨hy₁, hz₁nonunit, hw₁⟩ :=
    nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx₁ h₁
  obtain ⟨hy₂, _, hw₂⟩ :=
    nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx₂ h₂
  have hs : s < 1 := by
    rw [← hz₁val]
    exact A.mem_nonunits_iff.mpr hz₁nonunit
  have hl : l = (y₁ - y₂) / (x₁ - x₂) := by
    exact WeierstrassCurve.Affine.slope_of_X_ne hx
  have hy₁line : y₁ = l * x₁ + c := by simp only [c]; ring
  have hy₂line : y₂ = l * x₂ + c := by
    simp only [c]
    rw [hl]
    field_simp [sub_ne_zero.mpr hx]
    ring
  have hx₃line : x₃ = nosLineQ₂ W l - x₁ - x₂ := by
    simp only [x₃, WeierstrassCurve.Affine.addX, nosLineQ₂]
  have hy₃line : y₃ = l * x₃ + c := by
    simp only [y₃, WeierstrassCurve.Affine.negAddY, x₃, c]
    ring
  have hlocal₁ := nos_local_equation W h₁ hy₁
  have hlocal₂ := nos_local_equation W h₂ hy₂
  change nosLocalEquation W z₁ w₁ at hlocal₁
  change nosLocalEquation W z₂ w₂ at hlocal₂
  have hz₁lt : v z₁ < 1 := by rw [hz₁val]; exact hs
  have hz₂le : v z₂ ≤ v z₁ := by rw [hz₁val]; exact hz₂val
  have hUval := nos_chord_U_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hz₁lt hz₂le hw₁ hw₂
  have hU0 : nosChordU W z₁ w₁ w₂ ≠ 0 := by
    apply v.ne_zero_iff.mp
    change v (nosChordU W z₁ w₁ w₂) ≠ 0
    rw [hUval]
    exact one_ne_zero
  have hzneq := nos_chord_z_ne W hx hy₁ hy₂ rfl rfl rfl rfl hlocal₁ hlocal₂ hU0
  have hc0 := nos_line_intercept_ne hy₁ hy₂ hy₁line hy₂line hzneq
  have hw₁line : w₁ = a * z₁ + b := nos_transformed_line hy₁ hc0 hy₁line
  have hw₂line : w₂ = a * z₂ + b := nos_transformed_line hy₂ hc0 hy₂line
  obtain ⟨haeq, hbeq⟩ := nos_line_slope hzneq hw₁line hw₂line
  have habound : v a ≤ s ^ 2 := by
    rw [haeq]
    have hbound := nos_chord_slope_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hz₁lt hz₂le hw₁ hw₂
      hlocal₁ hlocal₂ hzneq
    change v ((w₂ - w₁) / (z₂ - z₁)) ≤ v z₁ ^ 2 at hbound
    rw [hz₁val] at hbound
    exact hbound
  have hbbound : v b ≤ s ^ 3 := by
    rw [hbeq]
    have hw₁s : v w₁ = s ^ 3 := by
      change v (-1 / y₁) = s ^ 3
      rw [hw₁, hz₁val]
    apply nos_line_intercept_bound A hz₁val hw₁s
    · exact habound
  have hr₁ := nos_line_root W h₁ hy₁line
  have hr₂ := nos_line_root W h₂ hy₂line
  obtain ⟨hs₂, hs₃⟩ := nos_secant_symmetric W hr₁ hr₂ hx
  have hs₁ : nosLineQ₂ W l = x₁ + x₂ + x₃ := by rw [hx₃line]; ring
  have hs₂' : nosLineQ₁ W l c = -(x₁ * x₂ + x₁ * x₃ + x₂ * x₃) := by
    simpa only [hx₃line] using hs₂
  have hs₃' : nosLineQ₀ W c = x₁ * x₂ * x₃ := by
    simpa only [hx₃line] using hs₃
  obtain ⟨hC₃, _⟩ := nos_line_coefficients_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hs habound hbbound
  have hC₃0 : nosLineC₃ W a ≠ 0 := by
    apply v.ne_zero_iff.mp
    change v (nosLineC₃ W a) ≠ 0
    rw [hC₃]
    exact one_ne_zero
  have hlead := nos_transformed_leading W hs₁ hs₂' hs₃' hy₁line hy₂line hy₃line hc0
  change nosLineC₃ W a = y₁ * y₂ * y₃ / c ^ 3 at hlead
  have hy₃ : y₃ ≠ 0 := by
    intro hyzero
    rw [hyzero, mul_zero, zero_div] at hlead
    exact hC₃0 hlead
  have hvieta := nos_secant_vieta W h₁ h₂ hx hy₁line hy₂line hy₃line hx₃line
    hy₁ hy₂ hy₃ hc0
  change nosLineC₃ W a * (z₁ + z₂ + z₃) + nosLineC₂ W a b = 0 at hvieta
  have hsum := nos_vieta_sum_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hs habound hbbound hvieta
  have h₃ := WeierstrassCurve.Affine.equation_negAdd h₁ h₂ (fun h ↦ hx h.1)
  have hw₃line : -1 / y₃ = a * z₃ + b := nos_transformed_line hy₃ hc0 hy₃line
  exact nos_finish_add W A ha₁ ha₂ ha₃ ha₄ ha₆ h₃ hy₃ rfl hw₃line hs0 hs
    hz₁val hz₂val habound hbbound hsum

lemma nos_tangent_add {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) (A : ValuationSubring K) {x y : K} {s : A.ValueGroup}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (h : WeierstrassCurve.Affine.Equation W x y) (hx : x ∉ A)
    (hyneg : y ≠ WeierstrassCurve.Affine.negY W x y) (hs0 : 0 < s)
    (hzval : A.valuation (-x / y) = s) :
    let l := WeierstrassCurve.Affine.slope W x x y y
    let x₃ := WeierstrassCurve.Affine.addX W x x l
    let y₃ := WeierstrassCurve.Affine.negAddY W x x y l
    x₃ ∉ A ∧ A.valuation
      (-x₃ / WeierstrassCurve.Affine.negY W x₃ y₃ - (-x / y) - (-x / y)) < s := by
  let v := A.valuation
  let z := -x / y
  let w := -1 / y
  let l := WeierstrassCurve.Affine.slope W x x y y
  let c := y - l * x
  let a := -l / c
  let b := -1 / c
  let x₃ := WeierstrassCurve.Affine.addX W x x l
  let y₃ := WeierstrassCurve.Affine.negAddY W x x y l
  let z₃ := -x₃ / y₃
  dsimp only
  change x₃ ∉ A ∧ v (-x₃ / WeierstrassCurve.Affine.negY W x₃ y₃ - z - z) < s
  obtain ⟨hy, hznonunit, hw⟩ :=
    nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx h
  have hs : s < 1 := by
    rw [← hzval]
    exact A.mem_nonunits_iff.mpr hznonunit
  have hden : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro hzero
    apply hyneg
    simp only [WeierstrassCurve.Affine.negY]
    linear_combination hzero
  have hl : l = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) /
      (2 * y + W.a₁ * x + W.a₃) := by
    change WeierstrassCurve.Affine.slope W x x y y = _
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
    congr 1
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hyline : y = l * x + c := by simp only [c]; ring
  have hx₃line : x₃ = nosLineQ₂ W l - 2 * x := by
    simp only [x₃, WeierstrassCurve.Affine.addX, nosLineQ₂]
    ring
  have hy₃line : y₃ = l * x₃ + c := by
    simp only [y₃, WeierstrassCurve.Affine.negAddY, x₃, c]
    ring
  have hlmul : l * (2 * y + W.a₁ * x + W.a₃) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hl]
    exact div_mul_cancel₀ _ hden
  have hderiv := nos_tangent_derivative_of_mul W rfl hlmul
  have hlocal := nos_local_equation W h hy
  change nosLocalEquation W z w at hlocal
  have hzlt : v z < 1 := by rw [hzval]; exact hs
  have hUval := nos_tangent_U_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hzlt hw
  have hU0 : nosChordU W z w w ≠ 0 := by
    apply v.ne_zero_iff.mp
    change v (nosChordU W z w w) ≠ 0
    rw [hUval]
    exact one_ne_zero
  obtain ⟨hc0, haeq, hbeq⟩ := nos_tangent_transform W h hy hden rfl rfl hl rfl hU0
  have habound : v a ≤ s ^ 2 := by
    change v (-l / c) ≤ s ^ 2
    rw [haeq]
    have hbound := nos_tangent_slope_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hzlt hw
    change v (nosChordV W z z w / nosChordU W z w w) ≤ v z ^ 2 at hbound
    rw [hzval] at hbound
    exact hbound
  have hbbound : v b ≤ s ^ 3 := by
    change v (-1 / c) ≤ s ^ 3
    rw [hbeq]
    have hws : v w = s ^ 3 := by
      change v (-1 / y) = s ^ 3
      rw [hw, hzval]
    have habound' : v (nosChordV W z z w / nosChordU W z w w) ≤ s ^ 2 := by
      rw [← haeq]
      exact habound
    exact nos_line_intercept_bound A hzval hws habound'
  have hroot := nos_line_root W h hyline
  obtain ⟨hs₂, hs₃⟩ := nos_tangent_symmetric W hroot hderiv
  have hs₁ : nosLineQ₂ W l = x + x + x₃ := by rw [hx₃line]; ring
  have hs₂' : nosLineQ₁ W l c = -(x * x + x * x₃ + x * x₃) := by
    simpa only [hx₃line] using hs₂
  have hs₃' : nosLineQ₀ W c = x * x * x₃ := by
    simpa only [hx₃line] using hs₃
  obtain ⟨hC₃, _⟩ := nos_line_coefficients_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hs habound hbbound
  have hC₃0 : nosLineC₃ W a ≠ 0 := by
    apply v.ne_zero_iff.mp
    change v (nosLineC₃ W a) ≠ 0
    rw [hC₃]
    exact one_ne_zero
  have hlead := nos_transformed_leading W hs₁ hs₂' hs₃' hyline hyline hy₃line hc0
  change nosLineC₃ W a = y * y * y₃ / c ^ 3 at hlead
  have hy₃ : y₃ ≠ 0 := by
    intro hyzero
    rw [hyzero, mul_zero, zero_div] at hlead
    exact hC₃0 hlead
  have hvieta := nos_tangent_vieta W h hyline hy₃line hx₃line hderiv hy hy₃ hc0
  change nosLineC₃ W a * (z + z + z₃) + nosLineC₂ W a b = 0 at hvieta
  have hsum := nos_vieta_sum_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hs habound hbbound hvieta
  have h₃ := WeierstrassCurve.Affine.equation_negAdd h h (fun hxy ↦ hyneg hxy.2)
  have hw₃line : -1 / y₃ = a * z₃ + b := nos_transformed_line hy₃ hc0 hy₃line
  exact nos_finish_add W A ha₁ ha₂ ha₃ ha₄ ha₆ h₃ hy₃ rfl hw₃line hs0 hs
    hzval hzval.le habound hbbound hsum

end MetaMathlibExt
