import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch8Entry12Qgammaintegers

open MeasureTheory
open Ramanujan.Part1Ch8.Entry12Qgammaintegers

/--
[Part1Ch8Entry12Qgammaintegers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry12Qgammaintegers.lean)
-/
@[path]
private lemma chapter8_unit_pow_eq_cpow_eq
-- given
  (x : ℂ)
  (u : ℝ)
  (hu : 0 < u) :
-- imply
  chapter8UnitPow x u = (u : ℂ) ^ x := by
-- proof
  apply Ramanujan.Part1Ch8.Entry12Qgammaintegers.chapter8UnitPow_eq_cpow x u hu

/--
[Part1Ch8Entry12Qgammaintegers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry12Qgammaintegers.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry12_qgamma_integers_cpow_eq
-- given
  (x : ℂ)
  (hx : 1 < x.re) :
-- imply
  (∀ j : ℕ,
    (((j : ℂ) + 1) * x) ^ 3 - ((j : ℂ) + 1) * x ≠ 0) ∧
    Summable (chapter8PhiTerm x) ∧
    chapter8Entry12Kernel x 0 = 0 ∧
    chapter8Entry12Kernel x 1 = 0 ∧
    (∀ u : ℝ,
      u ∈ Set.Ioo 0 1 →
        1 - (u : ℂ) ^ x ≠ 0 ∧
          chapter8Entry12Kernel x u =
            (u : ℂ) ^ (x - 2) * ((1 - u : ℝ) : ℂ) ^ 2 /
              (1 - (u : ℂ) ^ x)) ∧
    IntervalIntegrable (chapter8Entry12Kernel x) volume 0 1 ∧
    (∫ u in (0 : ℝ)..1, chapter8Entry12Kernel x u) =
      chapter8Phi x - 1 := by
-- proof
  apply Ramanujan.Part1Ch8.Entry12Qgammaintegers.ramanujan_part1_ch8_entry12_qgammaintegers_cpow x hx

/--
[Part1Ch8Entry12Qgammaintegers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry12Qgammaintegers.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry12_qgamma_integers_eq
-- given
  (x : ℂ)
  (hx : 1 < x.re) :
-- imply
  (∀ j : ℕ,
    (((j : ℂ) + 1) * x) ^ 3 - ((j : ℂ) + 1) * x ≠ 0) ∧
    Summable (chapter8PhiTerm x) ∧
    chapter8Entry12Kernel x 0 = 0 ∧
    chapter8Entry12Kernel x 1 = 0 ∧
    (∀ u : ℝ,
      u ∈ Set.Ioo 0 1 →
        1 - chapter8UnitPow x u ≠ 0 ∧
          chapter8Entry12Kernel x u =
            chapter8UnitPow (x - 2) u * ((1 - u : ℝ) : ℂ) ^ 2 /
              (1 - chapter8UnitPow x u)) ∧
    IntervalIntegrable (chapter8Entry12Kernel x) volume 0 1 ∧
    (∫ u in (0 : ℝ)..1, chapter8Entry12Kernel x u) =
      chapter8Phi x - 1 := by
-- proof
  apply Ramanujan.Part1Ch8.Entry12Qgammaintegers.ramanujan_part1_ch8_entry12_qgammaintegers x hx

-- created on 2026-10-10
