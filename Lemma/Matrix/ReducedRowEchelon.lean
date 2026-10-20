import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.ReducedRowEchelon
open Matrix.IsReducedRowEchelon
open MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted


/--
[col_eq_single_of_isLeadingEntry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma col_eq_single_of_isLeadingEntry_eq
  [Zero R] [One R] [DecidableEq m] [LinearOrder m] [LT n]
  {A : Matrix m n R}
  {i : m}
  {c : n}
-- given
  (hA : A.IsReducedRowEchelon)
  (hc : A.IsLeadingEntry i c) :
-- imply
  A.col c = Pi.single i 1 := by
-- proof
  apply Matrix.IsReducedRowEchelon.col_eq_single_of_isLeadingEntry hA hc

/--
[submatrix_orderIso](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma submatrix_orderIso_eq
  [Zero R] [One R] [LinearOrder m] [LinearOrder n] [LinearOrder o]
  {A : Matrix m n R}
-- given
  (hA : A.IsReducedRowEchelon)
  (e : o ≃o n) :
-- imply
  (A.submatrix id e : Matrix m o R).IsReducedRowEchelon := by
-- proof
  apply Matrix.IsReducedRowEchelon.submatrix_orderIso hA e

/--
[exists_isReducedRowEchelon_rowEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma exists_isReducedRowEchelon_rowEquivalent_eq
  [Field K] [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
  {A : Matrix m n K} :
-- imply
  ∃ (R : Matrix m n K) (P : Matrix m m K),
    R.IsReducedRowEchelon ∧ IsUnit P ∧ R = P * A := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted.exists_isReducedRowEchelon_rowEquivalent A

/--
[isReducedRowEchelon_unique_of_rowEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma isReducedRowEchelon_unique_of_rowEquivalent_eq
  [Field K] [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
  {R₁ R₂ : Matrix m n K}
  {P : Matrix m m K}
-- given
  (h₁ : R₁.IsReducedRowEchelon)
  (h₂ : R₂.IsReducedRowEchelon)
  (hP : IsUnit P)
  (h : R₂ = P * R₁) :
-- imply
  R₁ = R₂ := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted.isReducedRowEchelon_unique_of_rowEquivalent R₁ R₂ h₁ h₂ P hP h

/--
[ker_mulVecLin_mul_left_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma ker_mulVecLin_mul_left_isUnit_eq
  [Field K] [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
  {P : Matrix m m K}
  {A : Matrix m n K}
-- given
  (hP : IsUnit P) :
-- imply
  LinearMap.ker (Matrix.mulVecLin (P * A)) = LinearMap.ker (Matrix.mulVecLin A) := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted.ker_mulVecLin_mul_left_isUnit P A hP


-- created on 2026-10-20
