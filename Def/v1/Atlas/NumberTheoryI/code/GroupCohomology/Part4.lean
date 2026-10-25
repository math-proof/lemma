/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Instance.v1.Atlas.NumberTheoryI.code.GroupCohomology.Part2


noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

attribute [instance] FreeResolution.free

attribute [instance] IsAdditiveCategory.hasFiniteBiproducts

def cohomology_biprod_iso (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    groupCohomology (A ⊞ B) n ≅
    groupCohomology A n ⊞ groupCohomology B n := by
  open Limits in
  let F := groupCohomology.cochainsFunctor k G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n
  haveI : F.Additive := inferInstance
  haveI : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  haveI : PreservesBiproductsOfShape WalkingPair F := PreservesFiniteBiproducts.preserves
  haveI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapBiprod A B

def coinduced_def (k G : Type u) [CommRing k] [Group G] :
    Rep k ↥(⊥ : Subgroup G) ⥤ Rep k G :=
  Rep.coindFunctor k (⊥ : Subgroup G).subtype

def cohomology_coinduced_H0_iso
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupCohomology A 0 :=
  groupCohomology.coindIso A 0

end GroupCohomology
end
