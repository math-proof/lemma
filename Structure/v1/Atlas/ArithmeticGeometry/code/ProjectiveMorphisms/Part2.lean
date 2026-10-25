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
import Theorem.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- A projective rational function on a set $X \subseteq \mathbb{P}^n_k$: an equivalence class of homogeneous representatives, packaged as a maximal nonempty set of mutually equivalent `HomogeneousRep`s. -/
structure ProjectiveRatFun (n : ℕ) (k : Type*) [Field k]
    (X : Set (ℙ k (Fin (n + 1) → k))) where
  reps : Set (HomogeneousRep n k)
  reps_nonempty : reps.Nonempty
  reps_equiv : ∀ r₁ ∈ reps, ∀ r₂ ∈ reps, HomogeneousRep.equivOn k r₁ r₂ X
  reps_maximal : ∀ r, (∃ r₀ ∈ reps, HomogeneousRep.equivOn k r r₀ X) → r ∈ reps

end ProjectiveRegularFunction
end
