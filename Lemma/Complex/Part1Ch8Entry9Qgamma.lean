import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch8Entry9Qgamma

open MeasureTheory
open Ramanujan.Part1Ch8.Entry9Qgamma

/--
[Part1Ch8Entry9Qgamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry9Qgamma.lean)
-/
@[path]
private lemma chapter8_digamma_eq_digamma_eq
-- given
  (z : ℂ) :
-- imply
  chapter8Digamma z = Complex.digamma z := by
-- proof
  apply Ramanujan.Part1Ch8.Entry9Qgamma.chapter8Digamma_eq_digamma z

/--
[Part1Ch8Entry9Qgamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry9Qgamma.lean)
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
  apply Ramanujan.Part1Ch8.Entry9Qgamma.chapter8UnitPow_eq_cpow x u hu

/--
[Part1Ch8Entry9Qgamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry9Qgamma.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry9_qgamma_digamma_eq
-- given
  (x : ℂ)
  (hx : 0 < x.re) :
-- imply
  x ≠ 0 ∧
    IntervalIntegrable (chapter8UnitPowRatio x) volume 0 1 ∧
    (∀ u : ℝ, u ∈ Set.Icc 0 1 → 1 + chapter8UnitPow x u ≠ 0) ∧
    Complex.Gamma (1 / (2 * x) + 1) ≠ 0 ∧
    Complex.Gamma (1 / x + 1) ≠ 0 ∧
    Complex.digamma (1 / (2 * x) + 1) =
      Complex.digamma (1 / x + 1) - (Real.log 2 : ℂ) +
        x * ∫ u in (0 : ℝ)..1, chapter8UnitPowRatio x u := by
-- proof
  apply Ramanujan.Part1Ch8.Entry9Qgamma.ramanujan_part1_ch8_entry9_qgamma_digamma x hx

/--
[Part1Ch8Entry9Qgamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry9Qgamma.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry9_qgamma_eq
-- given
  (x : ℂ)
  (hx : 0 < x.re) :
-- imply
  x ≠ 0 ∧
    IntervalIntegrable (chapter8UnitPowRatio x) volume 0 1 ∧
    (∀ u : ℝ, u ∈ Set.Icc 0 1 → 1 + chapter8UnitPow x u ≠ 0) ∧
    Complex.Gamma (1 / (2 * x) + 1) ≠ 0 ∧
    Complex.Gamma (1 / x + 1) ≠ 0 ∧
    chapter8Digamma (1 / (2 * x) + 1) =
      chapter8Digamma (1 / x + 1) - (Real.log 2 : ℂ) +
        x * ∫ u in (0 : ℝ)..1, chapter8UnitPowRatio x u := by
-- proof
  apply Ramanujan.Part1Ch8.Entry9Qgamma.ramanujan_part1_ch8_entry9_qgamma x hx

-- created on 2026-10-10
