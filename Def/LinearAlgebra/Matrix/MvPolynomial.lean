/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff


namespace Matrix

open Polynomial

/-- The coefficient linear in a matrix direction in `det (B + X A)`, written as a sum of
determinants with one row replaced. -/
noncomputable def detLinear {n R : Type*}
    [Fintype n] [DecidableEq n] [CommRing R] (B A : Matrix n n R) : R :=
  ∑ i, det (updateRow B i (fun j ↦ A i j))

end Matrix
