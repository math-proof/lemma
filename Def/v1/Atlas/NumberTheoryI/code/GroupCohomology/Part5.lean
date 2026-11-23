/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Abbrev.v1.Atlas.NumberTheoryI.code.GroupCohomology.Part2

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

attribute [instance] FreeResolution.free

attribute [instance] IsAdditiveCategory.hasFiniteBiproducts

def homology_map {A B : Rep k G} (φ : A ⟶ B) (n : ℕ) :
    HomologyGroup A n ⟶ HomologyGroup B n :=
  groupHomology.map (MonoidHom.id G) φ n

def homologyFunctor (k : Type u) [CommRing k] (G : Type u) [Group G] (n : ℕ) :
    Rep k G ⥤ ModuleCat k :=
  groupHomology.functor k G n

def induced_def (k G : Type u) [CommRing k] [Group G] :
    Rep k ↥(⊥ : Subgroup G) ⥤ Rep k G :=
  Rep.indFunctor k (⊥ : Subgroup G).subtype

end GroupCohomology
end
