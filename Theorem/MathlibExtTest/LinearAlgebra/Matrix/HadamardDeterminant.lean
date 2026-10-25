/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/HadamardDeterminant.lean -/

/-
Author: Muse Spark 1.3
-/

import Lemma.Matrix.HadamardDeterminant
import Mathlib.Tactic.NormNum
open MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant

#check @hadamard_determinant_inequality


/-- Zero-dimensional case: the bound holds for every `0 × 0` matrix. -/
example (A : Matrix (Fin 0) (Fin 0) ℂ) :
    ‖A.det‖ ≤ ∏ i : Fin 0, Real.sqrt (∑ j : Fin 0, Complex.normSq (A i j)) :=
  hadamard_determinant_inequality A

/-- Zero-dimensional right-hand side is the empty product. -/
example : (∏ i : Fin 0, Real.sqrt
    (∑ j : Fin 0, Complex.normSq ((1 : Matrix (Fin 0) (Fin 0) ℂ) i j))) = 1 := by
  simp

