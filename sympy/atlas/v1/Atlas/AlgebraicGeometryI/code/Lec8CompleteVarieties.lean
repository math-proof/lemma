/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8CompleteVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ValuativeCriterion

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Formalization.Lec8CompleteVarieties


/-- A morphism `f : X ⟶ Y` is complete if it is separated and
universally closed (Lec 8, Def 19). -/
class IsComplete {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  isSeparated : IsSeparated f
  universallyClosed : UniversallyClosed f


/-- A proper morphism is complete. -/
instance isComplete_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    IsComplete f where
  isSeparated := inferInstance
  universallyClosed := inferInstance

/-- Two schemes are birational if they share a common dense open
subscheme (Lec 9 / Chow's lemma setting). -/
def IsBirational (X Y : Scheme.{u}) : Prop :=
  ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧
    Dense (Set.range f.base) ∧ Dense (Set.range g.base)

/-- A scheme `X` is projective if it admits a closed immersion into
some `Proj 𝒜` for a graded ring `𝒜` with finite-type degree-zero
piece (Lec 8/9, used for Chow's lemma). -/
def IsProjective (X : Scheme.{u}) : Prop :=
  ∃ (σ : Type u) (A : Type u)
    (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A)
    (𝒜 : ℕ → σ) (_ : GradedRing 𝒜) (_ : Algebra.FiniteType (𝒜 0) A)
    (i : X ⟶ Proj 𝒜), IsClosedImmersion i

/-- An affine scheme `U` admits an open immersion with dense image
into some projective scheme (input to Chow's lemma). -/
end Formalization.Lec8CompleteVarieties
