/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/WallSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers

set_option maxHeartbeats 0

open scoped InnerProductSpace
open Set

set_option maxHeartbeats 0

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HyperplaneArrangement

variable {arr : HyperplaneArrangement E}

/-- *The hyperplane $η$ separates two chambers $C, D$*: each of the two open half-spaces of
$η$ contains exactly one of $C, D$. -/
def SeparatesChambers (η : AffineHyperplane E) (_hη : η ∈ arr.hyperplanes)
    (C D : arr.Chamber) : Prop :=
  (C.set ⊆ η.positiveHalfSpace ∧ D.set ⊆ η.negativeHalfSpace) ∨
  (C.set ⊆ η.negativeHalfSpace ∧ D.set ⊆ η.positiveHalfSpace)

/-- *The chambers $C$ and $D$ are on the same side of $η$*: both lie in the positive
half-space, or both lie in the negative half-space. -/
def SameSide (η : AffineHyperplane E) (_hη : η ∈ arr.hyperplanes)
    (C D : arr.Chamber) : Prop :=
  (C.set ⊆ η.positiveHalfSpace ∧ D.set ⊆ η.positiveHalfSpace) ∨
  (C.set ⊆ η.negativeHalfSpace ∧ D.set ⊆ η.negativeHalfSpace)

/-- *Two chambers are adjacent along $η$*: they are distinct, are separated by $η$, and lie on
the same side of every other hyperplane. This is the natural geometric notion of "differing
only by a single wall reflection". -/
def AdjacentAlong (C D : arr.Chamber) (η : AffineHyperplane E) (hη : η ∈ arr.hyperplanes) :
    Prop :=
  C.set ≠ D.set ∧
  SeparatesChambers η hη C D ∧
  ∀ ξ ∈ arr.hyperplanes, ξ ≠ η →
    ∀ hξ : ξ ∈ arr.hyperplanes, SameSide ξ hξ C D

/-- *Adjacency of chambers*: there exists some hyperplane $η$ of `arr` along which $C$ and $D$
are adjacent. -/
def Adjacent (C D : arr.Chamber) : Prop :=
  ∃ η ∈ arr.hyperplanes, ∃ hη : η ∈ arr.hyperplanes, AdjacentAlong C D η hη
