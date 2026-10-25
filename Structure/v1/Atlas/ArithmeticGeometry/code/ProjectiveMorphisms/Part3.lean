/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Mathlib.Algebra.MvPolynomial.Monad
import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms.Part2


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- A tuple representative of a rational map $X \dashrightarrow Y$ between projective varieties: an $(n+1)$-tuple of homogeneous polynomials of common degree, not all vanishing on $X$, whose evaluation lands in $Y$ (as a projective point). -/
structure RationalMapTupleRep (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  polys : Fin (n + 1) → MvPolynomial (Fin (m + 1)) k
  deg : ℕ
  polys_homog : ∀ i, (polys i).IsHomogeneous deg
  not_all_vanish : ∃ i, ∃ P ∈ X, eval P.rep (polys i) ≠ 0
  image_in_Y : ∀ P ∈ X,
    (∃ i, eval P.rep (polys i) ≠ 0) →
    ∀ f : MvPolynomial (Fin (n + 1)) k,
    (∀ Q ∈ Y, eval Q.rep f = 0) →
    eval (fun j => eval P.rep (polys j)) f = 0

end ProjectiveRegularFunction
end
