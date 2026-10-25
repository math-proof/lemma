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
import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- A homogeneous representative is defined at a projective point $P$ if its denominator does not vanish at $P$. -/
def HomogeneousRep.isDefinedAt (r : HomogeneousRep n k)
    (P : ℙ k (Fin (n + 1) → k)) : Prop :=
  eval P.rep r.den ≠ 0

/-- Evaluate a homogeneous representative $\text{num}/\text{den}$ at a projective point $P$. Well-defined when the denominator is nonzero. -/
noncomputable def HomogeneousRep.evalAt (r : HomogeneousRep n k)
    (P : ℙ k (Fin (n + 1) → k)) : k :=
  eval P.rep r.num / eval P.rep r.den

/-- Two homogeneous representatives are equivalent on a set $X$ iff $\text{num}_1 \cdot \text{den}_2 - \text{num}_2 \cdot \text{den}_1$ vanishes on $X$ (i.e., they define the same rational function on $X$). -/
def HomogeneousRep.equivOn (r₁ r₂ : HomogeneousRep n k)
    (X : Set (ℙ k (Fin (n + 1) → k))) : Prop :=
  ∀ P ∈ X, eval P.rep (r₁.num * r₂.den - r₂.num * r₁.den) = 0

end ProjectiveRegularFunction
end
