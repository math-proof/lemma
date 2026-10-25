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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section35.Part12
open Set


/-- `absKFamily` together with `absKBond` is a directed system. -/
noncomputable instance CechCohomology.absKBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.absKFamily X K L p)
      fun i j h => CechCohomology.absKBond X K L p i j h where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_refl i.U))) p).hom.toAddMonoidHom x = x
    have hid : CechCohomology.opensInclusion (le_refl i.U) =
        𝟙 (TopCat.of ↑i.U.1) := by apply TopCat.ext; intro x; rfl
    have hres : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.U.1)) = 𝟙 _ := by
      simp only [SingularCohomology.restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    rw [hid, hres, HomologicalComplex.homologyMap_id]
    simp
  map_map := by
    intro k j i hij hjk x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.1)) p).hom.toAddMonoidHom
      ((HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion hij.1)) p).hom.toAddMonoidHom x) =
      (HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion (le_trans hjk.1 hij.1))) p).hom.toAddMonoidHom x
    have hcomp : CechCohomology.opensInclusion hjk.1 ≫ CechCohomology.opensInclusion hij.1 =
        CechCohomology.opensInclusion (le_trans hjk.1 hij.1) := by
      apply TopCat.ext; intro x; rfl
    rw [show SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_trans hjk.1 hij.1)) =
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hij.1) ≫
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.1)
      from by rw [← CechCohomology.restrictionCochainMap_comp, hcomp]]
    rw [HomologicalComplex.homologyMap_comp]
    simp [LinearMap.toAddMonoidHom_coe, ModuleCat.hom_comp]

