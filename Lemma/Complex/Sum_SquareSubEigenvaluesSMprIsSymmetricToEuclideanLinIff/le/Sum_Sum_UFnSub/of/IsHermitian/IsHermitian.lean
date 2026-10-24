import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.HoffmanWielandt


/--
[HoffmanWielandt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/HoffmanWielandt.lean)
-/
@[path]
private lemma hoffman_wielandt_hermitian_le
  {n : ℕ}
  {A B : Matrix (Fin n) (Fin n) ℂ}
-- given
  (hA : A.IsHermitian)
  (hB : B.IsHermitian) :
-- imply
  ∑ i : Fin n, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin i -
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues finrank_euclideanSpace_fin i) ^ 2 ≤
    ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j - B i j) := by
-- proof
  apply InnerProductSpace.HoffmanWielandtWanted.hoffman_wielandt_hermitian A B hA hB


-- created on 2026-10-10
-- updated on 2026-10-24
