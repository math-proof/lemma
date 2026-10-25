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
import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms.Part3


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- A tuple representative is defined at $P$ iff at least one coordinate polynomial is nonzero at $P$. -/
def RationalMapTupleRep.isDefinedAt
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : RationalMapTupleRep m n k X Y)
    (P : ℙ k (Fin (m + 1) → k)) : Prop :=
  ∃ i, eval P.rep (φ.polys i) ≠ 0

/-- The vector of values $(\varphi_0(P), \dots, \varphi_n(P))$ of a tuple representative at $P$. -/
noncomputable def RationalMapTupleRep.evalVec
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : RationalMapTupleRep m n k X Y)
    (P : ℙ k (Fin (m + 1) → k)) :
    Fin (n + 1) → k :=
  fun i => eval P.rep (φ.polys i)

/-- Two tuple representatives are equivalent on $X$ iff $\varphi_i \psi_j - \varphi_j \psi_i$ vanishes on $X$ for all $i, j$ (i.e., they define the same projective point at every point of $X$). -/
def RationalMapTupleRep.equivOn
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ ψ : RationalMapTupleRep m n k X Y)
    : Prop :=
  ∀ i j, ∀ P ∈ X,
    eval P.rep (φ.polys i * ψ.polys j - φ.polys j * ψ.polys i) = 0

end ProjectiveRegularFunction
end
