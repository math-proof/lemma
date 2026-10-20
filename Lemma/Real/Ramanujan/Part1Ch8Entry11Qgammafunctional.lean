import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch8Entry11Qgammafunctional
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch8
open Entry11Qgammafunctional


/--
[chapter8Digamma_eq_digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry11Qgammafunctional.lean)
-/
@[path]
private lemma chapter8Digamma_eq_digamma_eq
  {z : ℂ} :
-- imply
  chapter8Digamma z = Complex.digamma z := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry11Qgammafunctional.chapter8Digamma_eq_digamma z

/--
[chapter8PhiTerm_eq_entry12Qgammaintegers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry11Qgammafunctional.lean)
-/
@[path]
private lemma chapter8PhiTerm_eq_entry12Qgammaintegers_eq
  {x : ℂ}
  {j : ℕ} :
-- imply
  chapter8PhiTerm x j =
    chapter8PhiTerm x j := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry11Qgammafunctional.chapter8PhiTerm_eq_entry12Qgammaintegers x j

/--
[chapter8Phi_eq_entry12Qgammaintegers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry11Qgammafunctional.lean)
-/
@[path]
private lemma chapter8Phi_eq_entry12Qgammaintegers_eq
  {x : ℂ} :
-- imply
  chapter8Phi x =
    chapter8Phi x := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry11Qgammafunctional.chapter8Phi_eq_entry12Qgammaintegers x

/--
[ramanujan_part1_ch8_entry11_qgammafunctional_digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry11Qgammafunctional.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry11_qgammafunctional_digamma_eq
  {x : ℂ}
-- given
  (hx0 : x ≠ 0)
  (hpoles : ∀ k : ℕ, x ≠ 1 / ((k + 1 : ℕ) : ℂ) ∧ x ≠ -(1 / ((k + 1 : ℕ) : ℂ))) :
-- imply
  Summable (chapter8PhiTerm x) ∧
    Complex.Gamma (1 / x) ≠ 0 ∧
    Complex.Gamma (1 - 1 / x) ≠ 0 ∧
    Complex.digamma (1 / x) + Complex.digamma (1 - 1 / x) =
    -2 * (Real.eulerMascheroniConstant : ℂ) - x * chapter8Phi x := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry11Qgammafunctional.ramanujan_part1_ch8_entry11_qgammafunctional_digamma x hx0 hpoles

/--
[ramanujan_part1_ch8_entry11_qgammafunctional](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry11Qgammafunctional.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry11_qgammafunctional_eq
  {x : ℂ}
-- given
  (hx0 : x ≠ 0)
  (hpoles : ∀ k : ℕ, x ≠ 1 / ((k + 1 : ℕ) : ℂ) ∧ x ≠ -(1 / ((k + 1 : ℕ) : ℂ))) :
-- imply
  Summable (chapter8PhiTerm x) ∧
    Complex.Gamma (1 / x) ≠ 0 ∧
    Complex.Gamma (1 - 1 / x) ≠ 0 ∧
    chapter8Digamma (1 / x) + chapter8Digamma (1 - 1 / x) =
    -2 * (Real.eulerMascheroniConstant : ℂ) - x * chapter8Phi x := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry11Qgammafunctional.ramanujan_part1_ch8_entry11_qgammafunctional x hx0 hpoles


-- created on 2026-10-20
