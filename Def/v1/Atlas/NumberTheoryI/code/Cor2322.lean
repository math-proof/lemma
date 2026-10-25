/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2322.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Instance.v1.Atlas.NumberTheoryI.code.Cor2322
universe u


noncomputable def homology_biprod_iso (k G : Type u) [CommRing k] [Group G]
    (A B : Rep k G) (n : ℕ) :
    groupHomology (A ⊞ B) n ≅
    groupHomology A n ⊞ groupHomology B n := by
  open CategoryTheory Limits in
  let F := groupHomology.chainsFunctor k G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n
  haveI : F.Additive := inferInstance
  haveI : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  haveI : PreservesBiproductsOfShape WalkingPair F := PreservesFiniteBiproducts.preserves
  haveI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapBiprod A B

