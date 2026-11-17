/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19GradedQuotient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.DirectSum.Internal


@[expose] public noncomputable section

open DirectSum BigOperators

/-- The `n`-th piece `m^n / m^{n+1}` of the associated graded ring of `A` with respect to
an ideal `m`. -/
abbrev AssocGradedPiece {A : Type*} [CommRing A] (m : Ideal A) (n : ℕ) : Type _ :=
  (m ^ n : Submodule A A) ⧸ Submodule.comap (m ^ n).subtype (m ^ (n + 1))

end
