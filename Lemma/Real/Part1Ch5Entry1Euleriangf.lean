import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch5Entry1Euleriangf

open Ramanujan.Part1Ch5.Entry1Euleriangf
open Polynomial

/--
[Part1Ch5Entry1Euleriangf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry1Euleriangf.lean)
-/
@[path]
private lemma chapter5_polynomial_shift_eq_taylor_eq
  [Semiring R]
-- given
  (h : R)
  (p : R[X]) :
-- imply
  chapter5PolynomialShift h p = Polynomial.taylor h p := by
-- proof
  apply Ramanujan.Part1Ch5.Entry1Euleriangf.chapter5PolynomialShift_eq_taylor h p

/--
[Part1Ch5Entry1Euleriangf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry1Euleriangf.lean)
-/
@[path]
private lemma ramanujan_part1_ch5_entry1_euleriangf_eq :
-- imply
  (∀ (phi : ℝ[X]) (h : ℝ),
      chapter5PolynomialShift h (chapter5DerivativeExpansion chapter5Entry1PlusCoeff h phi) +
        chapter5DerivativeExpansion chapter5Entry1PlusCoeff h phi =
      Polynomial.C h * phi.derivative) ∧
    ∀ a : ℕ → ℝ,
      (∀ (phi : ℝ[X]) (h : ℝ),
          chapter5PolynomialShift h (chapter5DerivativeExpansion a h phi) +
            chapter5DerivativeExpansion a h phi =
          Polynomial.C h * phi.derivative) →
        a = chapter5Entry1PlusCoeff := by
-- proof
  apply Ramanujan.Part1Ch5.Entry1Euleriangf.ramanujan_part1_ch5_entry1_euleriangf

-- created on 2026-10-10
