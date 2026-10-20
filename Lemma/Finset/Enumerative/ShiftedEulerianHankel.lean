import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.ShiftedEulerianHankel
open MetaMathlibExt


/--
[hankel_transform_shifted_eulerian_polynomials](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ShiftedEulerianHankel.lean)
-/
@[path]
private lemma hankel_transform_shifted_eulerian_polynomials_eq
  :
-- imply
  ∀ (n : ℕ) (x : ℝ) (W : ℕ → ℕ → ℝ) (P : ℕ → ℝ → ℝ),
    (∀ (m k : ℕ),
    W m k =
    ∑ i ∈ Finset.range (m - k + 1),
    (-1 : ℝ) ^ i * ((((m + 1).choose i : ℕ) : ℝ)) *
    (((((m - k - i : ℕ) : ℝ))) ^ m)) →
    (∀ (m : ℕ) (X : ℝ),
    P m X = ∑ k ∈ Finset.range (m + 1), W m k * X ^ k) →
    Matrix.det (Matrix.of fun (i j : Fin (n + 1)) => P (i.val + j.val + 1) x) =
    (2 * x) ^ ((n + 1).choose 2) *
    ∏ k ∈ Finset.range n,
    (((((k + 3).choose 2 : ℕ) : ℝ)) ^ (n - (k + 1))) := by
-- proof
  apply MetaMathlibExt.hankel_transform_shifted_eulerian_polynomials


-- created on 2026-10-20
