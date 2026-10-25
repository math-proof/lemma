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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section35
open Set


namespace CechCohomology

open TopologicalSpace SingularCohomology CategoryTheory

variable {X : Type} [TopologicalSpace X]

open CategoryTheory.Limits in
/-- Transition map of relative singular cochain complexes induced by
`pair₁ ≤ pair₂`: the canonical map between kernels of the restriction cochain
maps coming from the commuting square. -/
noncomputable def relCochainComplexMap {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relativeSingularCochainComplex ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁) ⟶
    relativeSingularCochainComplex ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂) :=
  kernel.map
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.1))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.2))
    (restrictionCochainMap_square pair₁ pair₂ h)

/-- Transition map between relative singular cohomology groups
$H^p(U_1, V_1) \to H^p(U_2, V_2)$ for `pair₁ ≤ pair₂`, obtained by taking
$p$-th homology of `relCochainComplexMap`. -/
noncomputable def relCohomTransitionModMap {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) (p : ℕ) :
    relSingCohomOfPair pair₁ p ⟶ relSingCohomOfPair pair₂ p :=
  HomologicalComplex.homologyMap (relCochainComplexMap pair₁ pair₂ h) p

/-- Bonding map of the directed system `relCechFam K L p`: the underlying
additive group hom of `relCohomTransitionModMap`. -/
noncomputable def relCechTransitionMap
    {K L : Set X}
    (p : ℕ) (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relCechFam K L p pair₁ →+ relCechFam K L p pair₂ :=
  (relCohomTransitionModMap pair₁ pair₂ h p).hom.toAddMonoidHom

end CechCohomology
