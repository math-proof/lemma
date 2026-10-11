import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-! # Real power parametrization
-/

/-- Classical parametrization of distinct solutions to x ^ y = y ^ x with 0 < y < x.

Source: Hirotaka Kobayashi, Kota Saito, and Wataru Takeda, "Transcendence of
Values of the Iterated Exponential Function at Algebraic Points," Journal of
Integer Sequences 26 (2023), Article 23.3.3, Lemma (label add:lem1),
lines 604–612,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Takeda/tak6.tex>.

Proves `Wanted` entry `exists_parametrization_of_rpow_eq_rpow`.
-/
theorem exists_parametrization_of_rpow_eq_rpow (x y : ℝ) (hy : 0 < y) (hyx : y < x)
  (hxy : Real.rpow x y = Real.rpow y x) : ∃ (t : ℝ), 0 < t ∧
  (y = Real.rpow (1 + 1 / t) t ∧ x = Real.rpow (1 + 1 / t) (t + 1)) := by
  have hx : 0 < x := lt_trans hy hyx
  have hd : 0 < x - y := sub_pos.mpr hyx
  set t := y / (x - y) with ht
  have htpos : 0 < t := div_pos hy hd
  refine ⟨t, htpos, ?_⟩
  have hne_y : y ≠ 0 := ne_of_gt hy
  have hne_x : x ≠ 0 := ne_of_gt hx
  have hne_d : (x - y) ≠ 0 := ne_of_gt hd
  have hr : 1 + 1 / t = x / y := by
    rw [ht]
    field_simp
    ring
  have hrpos : 0 < x / y := div_pos hx hy
  have hrpos' : 0 < 1 + 1 / t := hr ▸ hrpos
  have e1 : Real.log (Real.rpow x y) = y * Real.log x := Real.log_rpow hx y
  have e2 : Real.log (Real.rpow y x) = x * Real.log y := Real.log_rpow hy x
  have hlog_eq : y * Real.log x = x * Real.log y := by
    have h1 : Real.log (Real.rpow x y) = Real.log (Real.rpow y x) := by rw [hxy]
    rw [e1, e2] at h1
    linarith
  have hlogdiv : Real.log (x / y) = Real.log x - Real.log y :=
    Real.log_div hne_x hne_y
  have hlogy : Real.log y = t * Real.log (x / y) := by
    rw [hlogdiv, ht]
    field_simp
    linear_combination -hlog_eq
  have hlogx : Real.log x = (t + 1) * Real.log (x / y) := by
    have h : Real.log x = Real.log y + Real.log (x / y) := by
      rw [hlogdiv]; ring
    rw [h, hlogy]; ring
  have r1 : Real.rpow (x / y) t = Real.exp (Real.log (x / y) * t) :=
    Real.rpow_def_of_pos hrpos t
  have r2 : Real.rpow (x / y) (t + 1) = Real.exp (Real.log (x / y) * (t + 1)) :=
    Real.rpow_def_of_pos hrpos (t + 1)
  have hy_eq : y = Real.rpow (x / y) t := by
    conv_lhs => rw [← Real.exp_log hy]
    rw [hlogy, r1]
    ring_nf
  have hx_eq : x = Real.rpow (x / y) (t + 1) := by
    conv_lhs => rw [← Real.exp_log hx]
    rw [hlogx, r2]
    ring_nf
  rw [← hr] at hy_eq hx_eq
  exact ⟨hy_eq, hx_eq⟩

end MetaMathlibExt
