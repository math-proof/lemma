/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModulesII.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Support
import Structure.v1.Atlas.LieGroups.code.DModuleApplications.Part5
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Def.v1.Atlas.LieGroups.code.DModulesII
open CategoryTheory


namespace DModulesII

section DModules

variable {R : Type*} [CommRing R] {D : Type*} [Ring D] (ι : R →+* D)

abbrev DModSupportedPred (I : Ideal R) : ObjectProperty (ModuleCat D) := fun M =>
  ∀ (f : R), f ∈ I → ∀ (v : M), ∃ N : ℕ, (ι f ^ N) • v = 0

abbrev DModSupportedCat (I : Ideal R) := (DModSupportedPred ι I).FullSubcategory

end DModules
end DModulesII
