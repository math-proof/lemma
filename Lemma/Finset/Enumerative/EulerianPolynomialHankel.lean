import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.EulerianPolynomialHankel
open MetaMathlibExt


/--
[eulerianPolynomial_hankelDeterminant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean)
-/
@[path]
private lemma eulerianPolynomial_hankelDeterminant_eq
  {P : ℕ → Polynomial ℤ}
  {n : ℕ}
-- given
  (hP : ∀ m : ℕ, P m = ∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (∑ i ∈ Finset.range (m - k + 1), (-1 : ℤ) ^ i * (Nat.choose (m + 1) i : ℤ) * ((m - k - i : ℕ) : ℤ) ^ m)) :
-- imply
  Matrix.det (fun i j : Fin (n + 1) => P (i.val + j.val)) =
    Polynomial.X ^ Nat.choose (n + 1) 2 *
    Polynomial.C (∏ k ∈ Finset.range n, ((Nat.factorial (k + 1) : ℤ) ^ 2)) := by
-- proof
  apply MetaMathlibExt.eulerianPolynomial_hankelDeterminant P hP n


-- created on 2026-10-20
