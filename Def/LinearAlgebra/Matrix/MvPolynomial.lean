/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

namespace Matrix

open Polynomial

/-- The coefficient linear in a matrix direction in `det (B + X A)`, written as a sum of
determinants with one row replaced. -/
noncomputable def detLinear {n R : Type*}
    [Fintype n] [DecidableEq n] [CommRing R] (B A : Matrix n n R) : R :=
  ∑ i, det (updateRow B i (fun j ↦ A i j))

end Matrix
