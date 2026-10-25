/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19GradedQuotient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.DirectSum.Internal
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec19GradedQuotient


noncomputable section

open DirectSum BigOperators

/-- The associated graded ring `gr_m(A) = ⨁_n m^n/m^{n+1}` of `A` with respect to `m`. -/
def AssocGraded {A : Type*} [CommRing A] (m : Ideal A) : Type _ :=
  ⨁ n, AssocGradedPiece m n

/-- The image (initial form in degree `p`) of an element `a ∈ m^p` inside the graded piece
`m^p/m^{p+1}`. -/
def imageInGradedPiece {A : Type*} [CommRing A] (m : Ideal A)
    (a : A) (p : ℕ) (ha : a ∈ m ^ p) : AssocGradedPiece m p :=
  Submodule.Quotient.mk ⟨a, ha⟩

/-- Include a single graded piece `m^p/m^{p+1}` into the associated graded ring. -/
def gradedPieceToAssocGraded {A : Type*} [CommRing A] (m : Ideal A)
    (p : ℕ) (x : AssocGradedPiece m p) : AssocGraded m :=
  DirectSum.of (AssocGradedPiece m) p x

/-- The image in the associated graded ring of an element `a ∈ m^p`, placed in degree `p`. -/
def imageInAssocGraded {A : Type*} [CommRing A] (m : Ideal A)
    (a : A) (p : ℕ) (ha : a ∈ m ^ p) : AssocGraded m :=
  gradedPieceToAssocGraded m p (imageInGradedPiece m a p ha)

/-- The image of an ideal `m` in the quotient ring `A / (a)`. -/
def quotientIdeal {A : Type*} [CommRing A] (m : Ideal A) (a : A) :
    Ideal (A ⧸ Ideal.span {a}) :=
  m.map (Ideal.Quotient.mk (Ideal.span {a}))

/-- The hypothesis used in Lemma 31/32 expressing that the initial form of `a` (an element of
`m^p`) is a non-zero-divisor in the associated graded ring: if `ax ∈ m^{k+p+1}` and
`x ∈ m^k`, then already `x ∈ m^{k+1}`. -/
def InitialFormNonZeroDivisor {A : Type*} [CommRing A] (m : Ideal A)
    (a : A) (p : ℕ) : Prop :=
  ∀ (k : ℕ) (x : A), x ∈ m ^ k → a * x ∈ m ^ (k + p + 1) → x ∈ m ^ (k + 1)

end
