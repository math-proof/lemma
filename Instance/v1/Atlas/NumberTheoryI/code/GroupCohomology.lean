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
import Class.v1.Atlas.NumberTheoryI.code.GroupCohomology


noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

attribute [instance] FreeResolution.free

attribute [instance] IsAdditiveCategory.hasFiniteBiproducts

instance (priority := 100) IsAdditiveCategory.toHasFiniteCoproducts
    (C : Type*) [Category C] [IsAdditiveCategory C] :
    Limits.HasFiniteCoproducts C :=
  inferInstance

instance (priority := 100) IsAdditiveCategory.toHasFiniteProducts
    (C : Type*) [Category C] [IsAdditiveCategory C] :
    Limits.HasFiniteProducts C :=
  inferInstance

instance (priority := 100) IsAdditiveCategory.toHasZeroObject
    (C : Type*) [Category C] [IsAdditiveCategory C] :
    Limits.HasZeroObject C :=
  Limits.hasZeroObject_of_hasFiniteBiproducts C

end GroupCohomology
end
