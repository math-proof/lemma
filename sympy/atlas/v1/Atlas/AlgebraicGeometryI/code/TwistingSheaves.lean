/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistingSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec14QCohProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec14QCohProjective

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The Serre twisting sheaf `O(d)` on `Proj 𝒜`, defined as the tilde of the
shifted graded module `R(d)`. -/
def twistingSheaf (d : ℤ) : (Proj 𝒜).Modules :=
  tildeProj 𝒜 (GrMod.shift 𝒜 d)

/-- Predicate: a sheaf of `O_X`-modules is locally free of rank `n`. -/
def degreePiece (d : ℕ) : AddSubgroup A where
  carrier := (𝒜 d : Set A)
  add_mem' ha hb := add_mem ha hb
  zero_mem' := zero_mem (𝒜 d)
  neg_mem' ha := neg_mem ha
