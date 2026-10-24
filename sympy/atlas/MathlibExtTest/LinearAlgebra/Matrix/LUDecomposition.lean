/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/LUDecomposition.lean -/


import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lemma.Matrix.LUDecomposition

open MathlibExt.LinearAlgebra.Matrix.LUDecompositionWanted

-- The leading minors of this concrete matrix are `1`, `2`, and `6`.
example :
    ∃ L U : Matrix (Fin 2) (Fin 2) ℚ,
      L.IsLowerTriangular ∧ U.IsUpperTriangular ∧ (∀ i, L i i = 1) ∧
        !![2, 1; 4, 5] = L * U := by
  apply exists_lu_decomposition_of_minors_ne_zero 2 !![2, 1; 4, 5]
  intro k hk
  interval_cases k <;> norm_num [Matrix.det_fin_two]

-- Any unit-lower/upper factorization of this matrix equals its concrete one.
example (L U : Matrix (Fin 2) (Fin 2) ℚ)
    (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular)
    (hd : ∀ i, L i i = 1) (hfac : !![2, 1; 4, 5] = L * U) :
    L = !![1, 0; 2, 1] ∧ U = !![2, 1; 0, 3] := by
  apply lu_decomposition_unique 2 !![2, 1; 4, 5] L !![1, 0; 2, 1] U !![2, 1; 0, 3]
  · norm_num [Matrix.det_fin_two]
  · exact hL
  · exact hU
  · exact hd
  · decide
  · decide
  · decide
  · exact hfac
  · norm_num [Matrix.mul_apply, Fin.sum_univ_two]
