import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.MvPolynomial
open Polynomial
open Matrix


/--
[det_add_smul_vecMulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean)
-/
@[path]
private lemma det_add_smul_vecMulVec_eq
  [Fintype n] [DecidableEq n] [Field K]
  {B : Matrix n n K}
  {u v : n → K}
  {t : K} :
-- imply
  det (B + t • vecMulVec u v) =
    det B + t * (det (B + vecMulVec u v) - det B) := by
-- proof
  apply Matrix.det_add_smul_vecMulVec B u v t

/--
[coeff_one_det_add_X_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean)
-/
@[path]
private lemma coeff_one_det_add_X_smul_eq
  [Fintype n] [DecidableEq n] [CommRing R]
  {B A : Matrix n n R} :
-- imply
  (det (B.map Polynomial.C + (Polynomial.X : R[X]) • A.map Polynomial.C)).coeff 1 =
    detLinear B A := by
-- proof
  apply Matrix.coeff_one_det_add_X_smul B A

/--
[detLinear_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean)
-/
@[path]
private lemma detLinear_add_eq
  [Fintype n] [DecidableEq n] [CommRing R]
  {B A C : Matrix n n R} :
-- imply
  detLinear B (A + C) = detLinear B A + detLinear B C := by
-- proof
  apply Matrix.detLinear_add B A C

/--
[detLinear_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean)
-/
@[path]
private lemma detLinear_smul_eq
  [Fintype n] [DecidableEq n] [CommRing R]
  {B A : Matrix n n R}
  {a : R} :
-- imply
  detLinear B (a • A) = a * detLinear B A := by
-- proof
  apply Matrix.detLinear_smul B A a


-- created on 2026-10-20
