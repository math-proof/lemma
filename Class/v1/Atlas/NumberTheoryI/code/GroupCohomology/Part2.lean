module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Instance.v1.Atlas.NumberTheoryI.code.GroupCohomology
public section


noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

attribute [instance] FreeResolution.free

attribute [instance] IsAdditiveCategory.hasFiniteBiproducts

class IsAdditiveFunctor {C : Type*} {D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) extends F.Additive

end GroupCohomology
end
