/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec18KahlerSmoothness.Part2
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000


@[expose] public noncomputable section

open IsLocalRing

/-- The local ring of the affine variety `V(I)` at the point `x`, obtained as the
localization of `k[x_1,…,x_n]/I` at the maximal ideal of `x`. -/
abbrev localRingAtPoint {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :=
  Localization.AtPrime (maxIdealOfPointInQuotient I x hI)

end
