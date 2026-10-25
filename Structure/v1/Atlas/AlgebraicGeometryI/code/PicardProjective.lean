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
import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- A homogeneous fraction: a pair of nonzero homogeneous polynomials of recorded
degrees, representing a section of a twist O(d) on projective space. -/
structure HomogFraction (σ : Type*) (k : Type*) [Field k] where
  num : MvPolynomial σ k
  den : MvPolynomial σ k
  num_ne : num ≠ 0
  den_ne : den ≠ 0
  ndeg : ℕ
  ddeg : ℕ
  nhom : num.IsHomogeneous ndeg
  dhom : den.IsHomogeneous ddeg

end PicardProjective
end
