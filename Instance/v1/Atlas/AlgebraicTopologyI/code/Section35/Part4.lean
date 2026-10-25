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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section35.Part5
open Set


open CategoryTheory CategoryTheory.Limits SingularCohomology in
/-- `relCechFam K L p` together with `relCechTransitionMap` is a directed
system: identities act as identities, and composition of bondings respects
composition of inclusions. -/
noncomputable instance CechCohomology.relCechFam_directedSystem_axioms
    {X : Type} [TopologicalSpace X] {K L : Set X} (p : ℕ) :
    DirectedSystem (CechCohomology.relCechFam K L p)
      (fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h) where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap (CechCohomology.relCochainComplexMap i i (le_refl i)) p).hom.toAddMonoidHom x = x
    have hid1 : CechCohomology.opensInclusion (le_refl i).1 =
        𝟙 (TopCat.of ↑i.U.1) := by apply TopCat.ext; intro x; rfl
    have hres1 : restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.U.1)) = 𝟙 _ := by
      simp only [restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    have hrelMap : CechCohomology.relCochainComplexMap i i (le_refl i) = 𝟙 _ := by
      unfold CechCohomology.relCochainComplexMap relativeSingularCochainComplex
      rw [← cancel_mono (kernel.ι (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i)))]
      simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
      rw [hid1]
      simp only [hres1, Category.comp_id]
    rw [hrelMap, HomologicalComplex.homologyMap_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    simp only [CechCohomology.relCechTransitionMap, CechCohomology.relCohomTransitionModMap]
    have hcomp1 : CechCohomology.opensInclusion hjk.1 ≫ CechCohomology.opensInclusion hij.1 =
        CechCohomology.opensInclusion (hij.trans hjk).1 := by
      apply TopCat.ext; intro x; rfl
    have hrelComp : CechCohomology.relCochainComplexMap i j hij ≫
        CechCohomology.relCochainComplexMap j k hjk =
        CechCohomology.relCochainComplexMap i k (hij.trans hjk) := by
      unfold CechCohomology.relCochainComplexMap relativeSingularCochainComplex
      rw [← cancel_mono (kernel.ι (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion k)))]
      simp only [Category.assoc, kernel.lift_ι]
      rw [kernel.lift_ι_assoc]
      simp only [Category.assoc, kernel.lift_ι]
      congr 1
      rw [← CechCohomology.restrictionCochainMap_comp, hcomp1]
    rw [show CechCohomology.relCochainComplexMap i k (hij.trans hjk) =
      CechCohomology.relCochainComplexMap i j hij ≫
      CechCohomology.relCochainComplexMap j k hjk from hrelComp.symm]
    rw [HomologicalComplex.homologyMap_comp]
    rfl

namespace CechCohomology

variable {X : Type} [TopologicalSpace X]

/-- Convenience instance form of `relCechFam_directedSystem_axioms`. -/
instance relCechFam_directedSystem {K L : Set X} (p : ℕ) :
    DirectedSystem (relCechFam K L p)
      (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h) :=
  relCechFam_directedSystem_axioms p

end CechCohomology
