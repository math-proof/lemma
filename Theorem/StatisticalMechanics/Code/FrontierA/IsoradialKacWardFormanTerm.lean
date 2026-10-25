/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part17
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanTerm


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finiteCRSF_atomicCycleSupports_biUnion {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    S.atomicCycles.biUnion (fun cycle => cycle.support) = Finset.univ := by
  rw [← S.restrictedPerm_support]
  ext v
  simp only [Finset.mem_biUnion, finiteCRSFCycleSupport.atomicCycles]
  exact (Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset).symm


theorem finiteCRSF_prod_transport_eq_prod_atomicCycleHolonomy
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    (∏ v ∈ S.carrier, transport v (next v)) =
      ∏ cycle ∈ S.atomicCycles,
        finiteCRSFAtomicCycleHolonomy transport S cycle := by
  rw [← Finset.prod_coe_sort S.carrier
    (fun v => transport v (next v))]
  change (∏ v ∈ (Finset.univ : Finset (↑S.carrier)),
      transport v (next v)) = _
  rw [← finiteCRSF_atomicCycleSupports_biUnion S]
  rw [Finset.prod_biUnion]
  · rfl
  · intro cycle hcycle cycle' hcycle' hne
    exact Equiv.Perm.disjoint_iff_disjoint_support.mp
      (S.restrictedPerm.cycleFactorsFinset_pairwise_disjoint
        hcycle hcycle' hne)


end StatMech.FrontierA
