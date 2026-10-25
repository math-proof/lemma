/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ShiftedEulerianHankel.lean -/


import Theorem.Combinatorics.Enumerative.ShiftedEulerianHankel
import Lemma.Finset.Enumerative.ShiftedEulerianHankel


namespace MetaMathlibExt

-- The theorem specializes directly to the order-three Hankel determinant.
example (x : ℝ) (W : ℕ → ℕ → ℝ) (P : ℕ → ℝ → ℝ)
    (hW : ∀ (m k : ℕ),
      W m k =
        ∑ i ∈ Finset.range (m - k + 1),
          (-1 : ℝ) ^ i * ((((m + 1).choose i : ℕ) : ℝ)) *
            (((((m - k - i : ℕ) : ℝ))) ^ m))
    (hP : ∀ (m : ℕ) (X : ℝ),
      P m X = ∑ k ∈ Finset.range (m + 1), W m k * X ^ k) :
    Matrix.det (Matrix.of fun (i j : Fin (2 + 1)) => P (i.val + j.val + 1) x) =
      (2 * x) ^ ((2 + 1).choose 2) *
        ∏ k ∈ Finset.range 2,
          (((((k + 3).choose 2 : ℕ) : ℝ)) ^ (2 - (k + 1))) := by
  exact hankel_transform_shifted_eulerian_polynomials 2 x W P hW hP

end MetaMathlibExt
