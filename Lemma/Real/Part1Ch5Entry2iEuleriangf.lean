import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch5Entry2iEuleriangf

open Polynomial
open Ramanujan.Part1Ch5.Entry2iEuleriangf

/--
[Part1Ch5Entry2iEuleriangf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry2iEuleriangf.lean)
-/
@[path]
private lemma chapter5_polynomial_shift_eq_taylor_eq
-- given
  {R : Type*}
  [Semiring R]
  (h : R)
  (p : R[X]) :
-- imply
  chapter5PolynomialShift h p = Polynomial.taylor h p := by
-- proof
  apply Ramanujan.Part1Ch5.Entry2iEuleriangf.chapter5PolynomialShift_eq_taylor h p

/--
[Part1Ch5Entry2iEuleriangf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry2iEuleriangf.lean)
-/
@[path]
private lemma ramanujan_part1_ch5_entry2i_eulerian_gf_eq
-- given
  (phi : ℝ[X]) :
-- imply
  (∀ n : ℕ, phi.natDegree < 2 * n → chapter5Entry2F phi n = 0) ∧
    chapter5PolynomialShift 1 (chapter5Entry2MinusSolution phi) -
      chapter5PolynomialShift (-1) (chapter5Entry2MinusSolution phi) =
    Polynomial.C 2 * phi.derivative ∧
    chapter5PolynomialShift 1 (chapter5Entry2PlusSolution phi) +
      chapter5PolynomialShift (-1) (chapter5Entry2PlusSolution phi) =
    Polynomial.C 2 * phi := by
-- proof
  apply Ramanujan.Part1Ch5.Entry2iEuleriangf.ramanujan_part1_ch5_entry2i_euleriangf phi

-- created on 2026-10-10
