/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Def.v1.Atlas.NumberTheoryI.code.Cor2328
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor2328


noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

section AugmentationMapAndIdeal

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

def augmentationMap : MonoidAlgebra k G →ₐ[k] k :=
  MonoidAlgebra.lift k k G 1

def augmentationIdeal : Ideal (MonoidAlgebra k G) :=
  RingHom.ker (augmentationMap k G).toRingHom

end AugmentationMapAndIdeal

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

def normMap (k : Type u) [CommRing k] (G : Type u) [Group G] [Fintype G]
    (A : Rep k G) : A →ₗ[k] A :=
  A.ρ.norm

def augmentationSubmodule (k : Type u) [CommRing k] (G : Type u) [Group G]
    (A : Rep k G) : Submodule k A :=
  Submodule.span k {x : A | ∃ (g : G) (a : A), x = A.ρ g a - a}

def GCoinvariants (k : Type u) [CommRing k] (G : Type u) [Group G]
    (A : Rep k G) : Type u :=
  A ⧸ (augmentationSubmodule k G A)

end TateCohomology
end
