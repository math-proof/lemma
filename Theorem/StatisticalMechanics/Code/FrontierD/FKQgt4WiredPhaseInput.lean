/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly.Part3
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4WiredPhaseInput
open MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem measurableSet_originIsolatedCylinder (d : Nat) :
    MeasurableSet (originIsolatedCylinder d) :=
  (isClopen_cylinderEvent _ _).1.measurableSet


theorem setPattern_mem_originIsolatedCylinder (d : Nat)
    (omega : ConfigSpace (Sym2 (Site d))) :
    FK.setPattern (originIncidentEdges d) (originIncidentClosedPattern d) omega ∈
      originIsolatedCylinder d := by
  rw [originIsolatedCylinder, MeasureTheory.mem_cylinder, Set.mem_singleton_iff]
  exact FK.setPattern_mem_patternEvent _ _ _


theorem cluster_origin_eq_singleton_of_mem_originIsolatedCylinder
    {d : Nat} {omega : ConfigSpace (Sym2 (Site d))}
    (homega : omega ∈ originIsolatedCylinder d) :
    cluster d omega (origin d) = {origin d} := by
  have hclosed : forall e, e ∈ originIncidentEdges d -> omega e = false := by
    intro e he
    rw [originIsolatedCylinder, MeasureTheory.mem_cylinder,
      Set.mem_singleton_iff] at homega
    have heq := congrFun homega ⟨e, he⟩
    simpa [originIncidentClosedPattern] using heq
  have hisolated : (openSubgraph d omega).neighborSet (origin d) = ∅ := by
    ext y
    constructor
    · intro hy
      have hopen : (hypercubicLattice d).Adj (origin d) y ∧
          omega s(origin d, y) = true := by
        simpa only [Set.mem_empty_iff_false, iff_false] using hy
      have hedge : s(origin d, y) ∈ originIncidentEdges d := by
        rw [originIncidentEdges, Finset.mem_image]
        exact ⟨y, (SimpleGraph.mem_neighborFinset _ _ _).2 hopen.1, rfl⟩
      rw [hclosed _ hedge] at hopen
      simp at hopen
    · simp
  apply Set.Subset.antisymm
  · intro y hy
    by_cases hyo : y = origin d
    · simpa [hyo]
    · exact absurd hy
        (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty (Ne.symm hyo) hisolated)
  · intro y hy
    simpa only [Set.mem_singleton_iff] using hy ▸ self_mem_cluster omega (origin d)


theorem originIsolatedCylinder_subset_percolationEvent_compl (d : Nat) :
    originIsolatedCylinder d ⊆ (percolationEvent d)ᶜ := by
  intro omega homega
  rw [Set.mem_compl_iff, mem_percolationEvent]
  rw [cluster_origin_eq_singleton_of_mem_originIsolatedCylinder homega]
  exact Set.not_infinite.mpr (Set.finite_singleton (origin d))


theorem wiredInfiniteVolume_originIsolatedCylinder_pos
    {d : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    0 < ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) (originIsolatedCylinder d) := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  let I := originIncidentEdges d
  let eta := originIncidentClosedPattern d
  have hac : mu.map (FK.setPattern I eta) ≪ mu := by
    exact FK.wiredInfinite_setPattern_absolutelyContinuous hp hp1 hq I eta
  have hpre : FK.setPattern I eta ⁻¹' originIsolatedCylinder d = Set.univ := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact setPattern_mem_originIsolatedCylinder d omega
  by_contra hnot
  rw [not_lt, nonpos_iff_eq_zero] at hnot
  have hzero := hac hnot
  rw [Measure.map_apply (FK.measurable_setPattern I eta)
      (measurableSet_originIsolatedCylinder d), hpre, measure_univ] at hzero
  exact one_ne_zero hzero


theorem wiredInfiniteVolume_percolationEvent_ne_one
    {d : Nat} {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) (percolationEvent d) ≠ 1 := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  intro hone
  have hcompl : mu ((percolationEvent d)ᶜ) = 0 :=
    (prob_compl_eq_zero_iff (FK.frp_measurableSet_percolationEvent d)).2 hone
  have hisolated : mu (originIsolatedCylinder d) = 0 :=
    nonpos_iff_eq_zero.mp <| (measure_mono
      (originIsolatedCylinder_subset_percolationEvent_compl d)).trans
        (le_of_eq hcompl)
  exact (ne_of_gt (wiredInfiniteVolume_originIsolatedCylinder_pos hp hp1 hq)) hisolated


end
end StatMech.FrontierD
