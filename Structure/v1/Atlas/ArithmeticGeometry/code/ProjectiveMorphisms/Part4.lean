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
import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms.Part3


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- Cleaner transitivity statement: on a projective variety $X$, `equivOn` is transitive (using primality of the vanishing ideal). -/
structure ProjectiveRationalMap (m n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (m + 1) → k)))
    (Y : Set (ℙ k (Fin (n + 1) → k))) where
  reps : Set (RationalMapTupleRep m n k X Y)
  reps_nonempty : reps.Nonempty
  reps_equiv : ∀ φ₁ ∈ reps, ∀ φ₂ ∈ reps, RationalMapTupleRep.equivOn k φ₁ φ₂
  reps_maximal : ∀ φ, (∃ φ₀ ∈ reps, RationalMapTupleRep.equivOn k φ φ₀) → φ ∈ reps

end ProjectiveRegularFunction
end
