/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/MvPolynomial.lean -/


import sympy.atlas.LinearAlgebra.Matrix.MvPolynomial
import Lemma.Matrix.MvPolynomial
import Mathlib.Basic.Complex.Basic


open Matrix

-- The rank-one determinant identity specializes to a nonzero one-dimensional update.
example :
    det (!![(2 : ℂ)] + (3 : ℂ) • vecMulVec ![(4 : ℂ)] ![(5 : ℂ)]) =
      det !![(2 : ℂ)] + 3 *
        (det (!![(2 : ℂ)] + vecMulVec ![(4 : ℂ)] ![(5 : ℂ)]) -
          det !![(2 : ℂ)]) :=
  Matrix.det_add_smul_vecMulVec !![(2 : ℂ)] ![(4 : ℂ)] ![(5 : ℂ)] 3

-- The linear determinant coefficient is detected in a concrete polynomial matrix.
example :
    let B : Matrix (Fin 1) (Fin 1) ℤ := !![2]
    let A : Matrix (Fin 1) (Fin 1) ℤ := !![3]
    (det (B.map Polynomial.C + (Polynomial.X : Polynomial ℤ) •
      A.map Polynomial.C)).coeff 1 =
      Matrix.detLinear B A := by
  dsimp only
  exact Matrix.coeff_one_det_add_X_smul !![2] !![3]

-- `detLinear` is additive on two nonzero one-dimensional directions.
example :
    Matrix.detLinear !![(2 : ℤ)] (!![(3 : ℤ)] + !![(5 : ℤ)]) =
      Matrix.detLinear !![(2 : ℤ)] !![(3 : ℤ)] +
        Matrix.detLinear !![(2 : ℤ)] !![(5 : ℤ)] :=
  Matrix.detLinear_add !![(2 : ℤ)] !![(3 : ℤ)] !![(5 : ℤ)]

-- `detLinear` is homogeneous on a nonzero one-dimensional direction.
example :
    Matrix.detLinear !![(2 : ℤ)] ((7 : ℤ) • !![(3 : ℤ)]) =
      7 * Matrix.detLinear !![(2 : ℤ)] !![(3 : ℤ)] :=
  Matrix.detLinear_smul !![(2 : ℤ)] !![(3 : ℤ)] 7
