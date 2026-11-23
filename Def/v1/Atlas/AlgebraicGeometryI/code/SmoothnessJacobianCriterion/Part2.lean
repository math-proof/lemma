/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessJacobianCriterion.lean -/

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
public import Instance.v1.Atlas.AlgebraicGeometryI.code.SmoothnessJacobianCriterion

@[expose] public section

noncomputable section

/-- Image of the point-maximal-ideal in the quotient `k[x]/I`: the maximal ideal
of the closed point `x` in the affine variety `V(I)`. -/
def maxIdealInQuotient_SJC {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (_ : I ≤ maxIdealOfPoint_SJC x) :
    Ideal (MvPolynomial (Fin n) k ⧸ I) :=
  Ideal.map (Ideal.Quotient.mk I) (maxIdealOfPoint_SJC x)

end
