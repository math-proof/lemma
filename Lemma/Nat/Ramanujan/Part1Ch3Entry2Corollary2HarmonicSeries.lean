import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry2Corollary2HarmonicSeries
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry2Corollary2HarmonicSeries


/--
[harmonic_eq_mathlib_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Corollary2HarmonicSeries.lean)
-/
@[path]
private lemma harmonic_eq_mathlib_harmonic_eq
  {n : ℕ} :
-- imply
  harmonic n = _root_.harmonic n := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Corollary2HarmonicSeries.harmonic_eq_mathlib_harmonic n

/--
[ramanujan_part1_ch3_entry2_corollary2_harmonic_series_mathlib](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Corollary2HarmonicSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry2_corollary2_harmonic_series_mathlib_eq
  {x : ℂ} :
-- imply
  Summable (fun j : ℕ => (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) /
    (Nat.factorial (j + 1) : ℂ)) ∧
    Summable (fun j : ℕ =>
    ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)))) ∧
    (∑' j : ℕ, (_root_.harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)) =
    Complex.exp x *
    (∑' j : ℕ,
    ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) *
    ((j + 1 : ℕ) : ℂ)))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Corollary2HarmonicSeries.ramanujan_part1_ch3_entry2_corollary2_harmonic_series_mathlib x

/--
[ramanujan_part1_ch3_entry2_corollary2_harmonic_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Corollary2HarmonicSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry2_corollary2_harmonic_series_eq
  {x : ℂ} :
-- imply
  Summable (fun j : ℕ => (harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)) ∧
    Summable (fun j : ℕ =>
    ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)))) ∧
    (∑' j : ℕ, (harmonic (j + 1) : ℂ) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ)) =
    Complex.exp x *
    (∑' j : ℕ,
    ((-1 : ℂ) ^ j * x ^ (j + 1) / ((Nat.factorial (j + 1) : ℂ) *
    ((j + 1 : ℕ) : ℂ)))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Corollary2HarmonicSeries.ramanujan_part1_ch3_entry2_corollary2_harmonic_series x


-- created on 2026-10-20
