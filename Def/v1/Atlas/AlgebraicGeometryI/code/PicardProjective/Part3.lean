/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part2


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The graded Picard group: equivalence classes of homogeneous fractions, modeling
Pic(P^n) by twisting sheaves up to isomorphism. -/
def GradedPicardGroup (σ : Type*) (k : Type*) [Field k] :=
  Quotient (homogFractionSetoid σ k)


end PicardProjective
end
