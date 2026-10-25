/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part11
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem frp_subset_oneStepClosure (K : FiniteRangeKernel d)
    (S : Finset (Site d)) : S ⊆ frpOneStepClosure K S :=
  Finset.subset_union_left

theorem frp_boundary_snd_mem_closure (K : FiniteRangeKernel d)
    (S : Finset (Site d)) {q : Site d × Site d}
    (hq : q ∈ frpBoundaryPairs K S) : q.2 ∈ frpOneStepClosure K S := by
  have hm := (mem_frpBoundaryPairs K S).mp hq
  let z := q.2 - q.1
  have hz : z ∈ frpSteps K := (mem_frpSteps K).mpr hm.2.2
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨(q.1, z), Finset.mem_product.mpr ⟨hm.1, hz⟩, ?_⟩
  simp [z]


theorem frp_exitEvent_eq_finite (K : FiniteRangeKernel d)
    (S : Finset (Site d)) (u : Site d) (huS : u ∈ S) :
    connEvent (frpGraph K) Set.univ u (S : Set (Site d))ᶜ =
      connEvent (frpGraph K) (frpOneStepClosure K S : Set (Site d))
        u (S : Set (Site d))ᶜ := by
  classical
  apply Set.Subset.antisymm
  · intro omega homega
    have hfirst := frp_firstExit_inclusion K Set.univ S
      (S : Set (Site d))ᶜ u huS (by simp)
    obtain ⟨q, hq, htriple⟩ := Set.mem_iUnion₂.mp (hfirst homega)
    have hparts := disjointOccurrence_subset_inter _ _ htriple
    have htail := disjointOccurrence_subset_inter _ _ hparts.2
    rcases hparts.1 with ⟨hu, x, hxS, hxeq, hconn⟩
    simp only [Set.mem_singleton_iff] at hxeq
    subst x
    have hqm := (mem_frpBoundaryPairs K S).mp hq
    have hSsub : (S : Set (Site d)) ⊆
        (frpOneStepClosure K S : Set (Site d)) := by
      intro z hz
      exact_mod_cast frp_subset_oneStepClosure K S hz
    have hconn' := frp_connWithin_mono_set K omega hSsub hconn
    have hxcl : q.1 ∈ frpOneStepClosure K S :=
      frp_subset_oneStepClosure K S hqm.1
    have hycl : q.2 ∈ frpOneStepClosure K S :=
      frp_boundary_snd_mem_closure K S hq
    have hedge : (openSub (frpGraph K) omega).Adj q.1 q.2 :=
      ⟨hqm.2.2, htail.1⟩
    have hedge' : ((openSub (frpGraph K) omega).induce
        (frpOneStepClosure K S : Set (Site d))).Adj
        ⟨q.1, hxcl⟩ ⟨q.2, hycl⟩ := hedge
    refine ⟨?_, q.2, ?_, ?_, hconn'.trans hedge'.reachable⟩
    · exact_mod_cast frp_subset_oneStepClosure K S huS
    · exact_mod_cast hycl
    · rw [Set.mem_compl_iff]
      exact_mod_cast hqm.2.1
  · rintro omega ⟨hu, z, hz, hzout, hconn⟩
    exact ⟨Set.mem_univ _, z, Set.mem_univ _, hzout,
      frp_connWithin_mono_set K omega (Set.subset_univ _) hconn⟩

theorem frp_exitEvent_dependsOn (K : FiniteRangeKernel d)
    (S : Finset (Site d)) (u : Site d) (huS : u ∈ S) :
    DependsOn (connEvent (frpGraph K) Set.univ u (S : Set (Site d))ᶜ)
      (frpInternalEdges (frpOneStepClosure K S) : Set (Sym2 (Site d))) := by
  rw [frp_exitEvent_eq_finite K S u huS]
  exact frp_connEvent_set_dependsOn K (frpOneStepClosure K S) u
    (S : Set (Site d))ᶜ

theorem measurableSet_frp_exitEvent (K : FiniteRangeKernel d)
    (S : Finset (Site d)) (u : Site d) (huS : u ∈ S) :
    MeasurableSet (connEvent (frpGraph K) Set.univ u (S : Set (Site d))ᶜ) :=
  measurableSet_of_dependsOn
    (ih_indicator_dependsOn_of_event (frp_exitEvent_dependsOn K S u huS))


theorem frpGraph_adj_smul (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d)) (x y : Site d) :
    (frpGraph K).Adj (g • x) (g • y) ↔ (frpGraph K).Adj x y := by
  have hcouple := frpEdgeCoupling_smul K g s(x, y)
  rw [smul_sym2_mk, frpEdgeCoupling_mk, frpEdgeCoupling_mk] at hcouple
  change 0 < K.coupling (g • y - g • x) ↔ 0 < K.coupling (y - x)
  rw [hcouple]

theorem frp_openSub_adj_shift (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    (openSub (frpGraph K) (shift g omega)).Adj (g • x) (g • y) ↔
      (openSub (frpGraph K) omega).Adj x y := by
  simp only [openSub]
  rw [frpGraph_adj_smul, shift_apply_smul]

end Sharpness
end StatMech
