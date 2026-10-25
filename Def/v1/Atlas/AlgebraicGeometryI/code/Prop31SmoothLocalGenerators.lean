/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop31SmoothLocalGenerators.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps


noncomputable section

/-- The maximal ideal of polynomials in `k[X_1, ..., X_n]` vanishing at the point `x`. -/
def maxIdealOfPoint_P31 {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : Ideal (MvPolynomial (Fin n) k) :=
  RingHom.ker (MvPolynomial.eval x)

end
