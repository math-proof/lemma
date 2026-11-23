/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop31SmoothLocalGenerators.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Prop31SmoothLocalGenerators

@[expose] public section

noncomputable section

/-- The Jacobian matrix of `f_1, ..., f_m ∈ k[X_1, ..., X_n]` at the point `x ∈ k^n`. -/
def jacobianMatrix_P31 {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (x : Fin n → k) :
    Matrix (Fin m) (Fin n) k :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i))

end
