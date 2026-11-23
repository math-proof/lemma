/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/NarayanaPolynomial.lean -/
module

public import Def.Combinatorics.Enumerative.NarayanaPolynomial
public import Theorem.Finset.Enumerative.NarayanaPolynomial
public import Mathlib.Tactic.Ring

public section

namespace MetaMathlibExt

example : narayanaPolynomial ℕ 0 = 1 := by
  simp [narayanaPolynomial, narayanaPolynomialCoeff]

example : narayanaPolynomial ℕ 1 = Polynomial.X := by
  simp [narayanaPolynomial, narayanaPolynomialCoeff, narayana, Finset.sum_range_succ]

example : narayanaPolynomial ℕ 2 = Polynomial.X ^ 2 + Polynomial.X := by
  simp [narayanaPolynomial, narayanaPolynomialCoeff, narayana, Finset.sum_range_succ]
  ac_rfl

example : narayanaPolynomial ℕ 3 =
    Polynomial.X ^ 3 + 3 * Polynomial.X ^ 2 + Polynomial.X := by
  simp [narayanaPolynomial, narayanaPolynomialCoeff, narayana, Finset.sum_range_succ]
  ring

end MetaMathlibExt
