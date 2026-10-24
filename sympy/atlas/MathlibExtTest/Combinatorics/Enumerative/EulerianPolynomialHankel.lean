/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/EulerianPolynomialHankel.lean -/


import sympy.atlas.Combinatorics.Enumerative.EulerianPolynomialHankel
import Lemma.Finset.Enumerative.EulerianPolynomialHankel

section
namespace MetaMathlibExt

-- The theorem specializes directly to the four-by-four Hankel matrix.
example (P : ℕ → Polynomial ℤ)
    (hP : ∀ m : ℕ, P m =
      ∑ k ∈ Finset.range (m + 1),
        Polynomial.monomial k
          (∑ i ∈ Finset.range (m - k + 1),
            (-1 : ℤ) ^ i * (Nat.choose (m + 1) i : ℤ) *
              ((m - k - i : ℕ) : ℤ) ^ m)) :
    Matrix.det (fun i j : Fin (3 + 1) ↦ P (i.val + j.val)) =
      Polynomial.X ^ Nat.choose (3 + 1) 2 *
        Polynomial.C (∏ k ∈ Finset.range 3, ((Nat.factorial (k + 1) : ℤ) ^ 2)) := by
  exact eulerianPolynomial_hankelDeterminant P hP 3

end MetaMathlibExt
end
