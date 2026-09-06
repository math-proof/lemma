import sympy.matrices.determinant


@[main]
private lemma main
  [CommRing α]
-- given
  (X : Tensor α [n, n]) :
-- imply
  X.det = X.toMatrix.det := by
-- proof
  unfold Tensor.det
  split_ifs with h_gt h_lt
  ·
    simp at h_gt
  ·
    simp at h_lt
  ·
    simp


-- created on 2026-09-06
