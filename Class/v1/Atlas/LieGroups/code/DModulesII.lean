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
import Def.v1.Atlas.LieGroups.code.DModulesII.Part2
open CategoryTheory


namespace DModulesII

section DModules

variable {R : Type*} [CommRing R] {D : Type*} [Ring D] (ι : R →+* D)

class IsLeibnizCompatible (ι : R →+* D) (M : Type*) [AddCommGroup M] [Module D M] : Prop where
  smul_torsion : ∀ (d : D) (f : R) (m : M) (n : ℕ),
    (ι f ^ n) • m = 0 → ∃ N : ℕ, (ι f ^ N) • (d • m) = 0

class IsKashiwaraSetup
    {R : Type*} [CommRing R] {D : Type*} [Ring D] (_ : R →+* D)
    (I : Ideal R) (D' : Type*) [Ring D'] (ι' : R ⧸ I →+* D') : Prop where
  isSmooth_X : IsNoetherian R R
  isSmooth_Z : IsNoetherian (R ⧸ I) (R ⧸ I)
  ι'_injective : Function.Injective ι'

end DModules
end DModulesII
