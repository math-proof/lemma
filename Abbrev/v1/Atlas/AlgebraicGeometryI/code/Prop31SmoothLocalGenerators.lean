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
public import Instance.v1.Atlas.AlgebraicGeometryI.code.Prop31SmoothLocalGenerators.Part2


@[expose] public noncomputable section

/-- The local ring of the variety `V(I)` at the point `x`. -/
abbrev localRingAtPoint_P31 {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_P31 x) :=
  Localization.AtPrime (maxIdealInQuotient_P31 I x hI)

end
