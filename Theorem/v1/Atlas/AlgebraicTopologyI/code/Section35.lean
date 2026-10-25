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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section35.Part4
open Set


namespace CechCohomology

open TopologicalSpace SingularCohomology CategoryTheory

variable {X : Type} [TopologicalSpace X]

/-- Naturality square for opens inclusions: the two ways of composing the
inclusions $V_2 \hookrightarrow V_1 \hookrightarrow U_1$ and
$V_2 \hookrightarrow U_2 \hookrightarrow U_1$ agree. -/
theorem opensInclusion_comm {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    opensInclusion h.2 ≫ relNbhdInclusion pair₁ =
    relNbhdInclusion pair₂ ≫ opensInclusion h.1 := by
  apply TopCat.ext
  intro x
  rfl

/-- The cochain-restriction operation is contravariantly functorial in
composition of continuous maps. -/
theorem restrictionCochainMap_comp (R : Type) [CommRing R]
    (G : ModuleCat.{0} R) {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    restrictionCochainMap R G (f ≫ g) =
    restrictionCochainMap R G g ≫ restrictionCochainMap R G f := by
  simp only [restrictionCochainMap, Functor.map_comp]
  rfl

/-- Commutativity of restriction cochain maps along the square of inclusions
associated to `pair₁ ≤ pair₂`: derives from `opensInclusion_comm` and the
contravariant functoriality of restriction. -/
theorem restrictionCochainMap_square {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁) ≫
      restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.2) =
    restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.1) ≫
      restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂) := by
  rw [← restrictionCochainMap_comp, ← restrictionCochainMap_comp,
      opensInclusion_comm pair₁ pair₂ h]

end CechCohomology
