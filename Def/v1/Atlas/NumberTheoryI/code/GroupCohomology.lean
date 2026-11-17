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
public import Abbrev.v1.Atlas.NumberTheoryI.code.GroupCohomology

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

def cochainComplexMap {A B : Rep k G} (φ : A ⟶ B) :
    cochainComplex A ⟶ cochainComplex B :=
  groupCohomology.cochainsMap (MonoidHom.id G) φ

def cohomology_map {A B : Rep k G} (φ : A ⟶ B) (n : ℕ) :
    CohomologyGroup A n ⟶ CohomologyGroup B n :=
  groupCohomology.map (MonoidHom.id G) φ n

end GroupCohomology
end
