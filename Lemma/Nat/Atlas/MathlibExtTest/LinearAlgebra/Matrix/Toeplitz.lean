import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.LinearAlgebra.Matrix.Toeplitz.Part3
open MetaMathlibExt


/--
[toeplitz3_isToeplitz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean)
-/
@[path]
private lemma toeplitz3_isToeplitz : IsToeplitzMatrix toeplitz3 := by
  refine isToeplitzMatrix_of_witness (c := fun k : ℤ =>
    if k = 0 then (1 : ℝ) else if k = 1 then 4 else if k = -1 then 2 else
      if k = 2 then 5 else if k = -2 then 3 else 0) ?_
  intro i j
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num [toeplitz3]

/--
[symm3_isSymmToeplitz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/Toeplitz.lean)
-/
@[path]
private lemma symm3_isSymmToeplitz : IsSymmetricToeplitzMatrix symm3 := by
  refine isSymmetricToeplitzMatrix_of_witness
    (c := fun k : ℤ => (k : ℝ) * (k : ℝ) + 1) ?_ ?_
  · intro k
    rw [Int.cast_neg, neg_mul_neg]
  · intro i j
    fin_cases i
    all_goals fin_cases j
    all_goals norm_num [symm3]


-- created on 2026-10-23
