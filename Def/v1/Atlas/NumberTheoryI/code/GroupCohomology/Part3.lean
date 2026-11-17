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
public import Structure.v1.Atlas.NumberTheoryI.code.GroupCohomology.Part2

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

attribute [instance] FreeResolution.free

def barComplex_iso_standardComplex (k G : Type u) [CommRing k] [Group G] :
    Rep.barComplex k G ≅ Rep.standardComplex k G :=
  Rep.barComplex.isoStandardComplex k G

def cohomology_iso_ext (A : Rep k G) (n : ℕ) :
    CohomologyGroup A n ≅
    ((Ext k (Rep k G) n).obj (Opposite.op (Rep.trivial k G k))).obj A :=
  groupCohomologyIsoExt A n

end GroupCohomology
end
