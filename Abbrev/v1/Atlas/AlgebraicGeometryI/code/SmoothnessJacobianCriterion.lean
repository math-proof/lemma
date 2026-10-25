/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessJacobianCriterion.lean -/

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
import Instance.v1.Atlas.AlgebraicGeometryI.code.SmoothnessJacobianCriterion.Part2


noncomputable section

/-- The **local ring at a `k`-rational point** `x` of an affine variety `V(I)`:
the localization of `k[x]/I` at the maximal ideal of `x`. -/
abbrev localRingAtPoint_SJC {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_SJC x) :=
  Localization.AtPrime (maxIdealInQuotient_SJC I x hI)

end
