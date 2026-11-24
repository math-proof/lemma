module
public import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The degree map is additive: deg(L ⊗ M) = deg(L) + deg(M). -/
lemma degreeMap_add (σ : Type*) (k : Type*) [Field k]
    (a b : GradedPicardGroup σ k) :
    GradedPicardGroup.degreeMap σ k (a + b) =
      GradedPicardGroup.degreeMap σ k a + GradedPicardGroup.degreeMap σ k b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i p q
  show (p.mul σ k q).degree σ k = p.degree σ k + q.degree σ k
  simp only [HomogFraction.degree, HomogFraction.mul]
  push_cast; ring

end PicardProjective
end
