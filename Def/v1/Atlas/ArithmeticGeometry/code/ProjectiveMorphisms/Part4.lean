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
import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms.Part4


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- A projective rational map is regular at $P \in X$ iff some representative is defined at $P$. -/
def ProjectiveRationalMap.IsRegularAt
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y)
    (P : ℙ k (Fin (m + 1) → k))
    (_hP : P ∈ X) : Prop :=
  ∃ rep ∈ φ.reps, rep.isDefinedAt k P

/-- The regular domain of a projective rational map: the locus of points of $X$ where it is regular. -/
def ProjectiveRationalMap.regularDomain
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) :
    Set (ℙ k (Fin (m + 1) → k)) :=
  {P ∈ X | ∃ rep ∈ φ.reps, rep.isDefinedAt k P}


/-- A projective rational map is a morphism iff it is regular at every point of its domain $X$. -/
def ProjectiveRationalMap.IsMorphism
    {X : Set (ℙ k (Fin (m + 1) → k))}
    {Y : Set (ℙ k (Fin (n + 1) → k))}
    (φ : ProjectiveRationalMap m n k X Y) : Prop :=
  ∀ (P : ℙ k (Fin (m + 1) → k)) (hP : P ∈ X), φ.IsRegularAt k P hP


end ProjectiveRegularFunction
end
