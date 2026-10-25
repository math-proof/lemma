/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Colimit.Module
import Mathlib.Order.Cofinal
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Def.v1.Atlas.AlgebraicTopologyI.code.Section35.Part13
open Set


/-- `absLFamily` together with `absLBond` is a directed system. -/
noncomputable instance CechCohomology.absLBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.absLFamily X K L p)
      fun i j h => CechCohomology.absLBond X K L p i j h where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_refl i.V))) p).hom.toAddMonoidHom x = x
    have hid : CechCohomology.opensInclusion (le_refl i.V) =
        𝟙 (TopCat.of ↑i.V.1) := by apply TopCat.ext; intro x; rfl
    have hres : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.V.1)) = 𝟙 _ := by
      simp only [SingularCohomology.restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    rw [hid, hres, HomologicalComplex.homologyMap_id]
    simp
  map_map := by
    intro k j i hij hjk x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.2)) p).hom.toAddMonoidHom
      ((HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion hij.2)) p).hom.toAddMonoidHom x) =
      (HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion (le_trans hjk.2 hij.2))) p).hom.toAddMonoidHom x
    have hcomp : CechCohomology.opensInclusion hjk.2 ≫ CechCohomology.opensInclusion hij.2 =
        CechCohomology.opensInclusion (le_trans hjk.2 hij.2) := by
      apply TopCat.ext; intro x; rfl
    rw [show SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_trans hjk.2 hij.2)) =
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hij.2) ≫
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.2)
      from by rw [← CechCohomology.restrictionCochainMap_comp, hcomp]]
    rw [HomologicalComplex.homologyMap_comp]
    simp [LinearMap.toAddMonoidHom_coe, ModuleCat.hom_comp]


