/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorVanishing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
import Theorem.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

theorem twoArmDisconnectedTraceEvent_real_tendsto_zero
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0)
    (x y : Site d) :
    Tendsto (fun m => (mu : Measure _).real
      (twoArmDisconnectedTraceEvent m x y)) atTop (nhds 0) := by
  obtain ⟨R, hR⟩ := Percolation.finite_subset_box
    ({x, y} : Set (Site d)) (Set.toFinite _)
  have hxR : x ∈ box d R := hR (by simp)
  have hyR : y ∈ box d R := hR (by simp)
  have htail : Antitone
      (fun n => twoArmDisconnectedTraceEvent (R + n + 1) x y) :=
    twoArmDisconnectedTraceEvent_tail_antitone hxR hyR
  have hmeas : ∀ n, NullMeasurableSet
      (twoArmDisconnectedTraceEvent (R + n + 1) x y) (mu : Measure _) :=
    fun n => (isClopen_twoArmDisconnectedTraceEvent
      (R + n + 1) x y).isOpen.measurableSet.nullMeasurableSet
  have hdistinct : (mu : Measure _) (distinctInfiniteClusterEvent x y) = 0 :=
    measure_mono_null (distinctInfiniteClusterEvent_subset_atLeastTwoInfinite x y)
      hunique
  have htailMeasure : Tendsto
      (fun n => (mu : Measure _)
        (twoArmDisconnectedTraceEvent (R + n + 1) x y))
      atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop (μ := (mu : Measure _)) hmeas htail
      ⟨0, measure_ne_top (mu : Measure _)
        (twoArmDisconnectedTraceEvent (R + 0 + 1) x y)⟩
    rw [iInter_twoArmDisconnectedTraceEvent hxR hyR, hdistinct] at h
    exact h
  have htailReal : Tendsto
      (fun n => (mu : Measure _).real
        (twoArmDisconnectedTraceEvent (R + n + 1) x y))
      atTop (nhds 0) := (ENNReal.tendsto_toReal (by simp)).comp htailMeasure
  exact (tendsto_add_atTop_iff_nat (R + 1)).1 (by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htailReal)

theorem twoOddCrossClustersEvent_subset_twoArmUnion
    (m : Nat) (hm : 1 ≤ m) (A B : Finset (Site d))
    (hA : (A : Set (Site d)) ⊆ box d (m - 1))
    (hB : (B : Set (Site d)) ⊆ (box d (m - 1))ᶜ) :
    twoOddCrossClustersEvent (hypercubicLattice d) A B ⊆
      ⋃ x ∈ A, ⋃ y ∈ A, twoArmDisconnectedTraceEvent m x y := by
  classical
  intro omega homega
  obtain ⟨C1, C2, hne, hC1A, hC1B, hC2A, hC2B⟩ := homega
  have pick {C : (openSub (hypercubicLattice d) omega).ConnectedComponent}
      {S : Finset (Site d)} (hodd : Odd
        (clusterMarkCount (hypercubicLattice d) omega S C)) :
      ∃ x ∈ S, (openSub (hypercubicLattice d) omega).connectedComponentMk x = C := by
    have hmem := mem_markedComponents_of_odd_clusterMarkCount
      (hypercubicLattice d) omega S C hodd
    simpa only [markedComponents, Finset.mem_image] using hmem
  obtain ⟨x1, hx1A, hx1C⟩ := pick hC1A
  obtain ⟨y1, hy1B, hy1C⟩ := pick hC1B
  obtain ⟨x2, hx2A, hx2C⟩ := pick hC2A
  obtain ⟨y2, hy2B, hy2C⟩ := pick hC2B
  have hx1y1 : Connected d omega x1 y1 := by
    exact SimpleGraph.ConnectedComponent.eq.mp (hx1C.trans hy1C.symm)
  have hx2y2 : Connected d omega x2 y2 := by
    exact SimpleGraph.ConnectedComponent.eq.mp (hx2C.trans hy2C.symm)
  have hnotx : ¬Connected d omega x1 x2 := by
    intro hconn
    apply hne
    rw [← hx1C, ← hx2C]
    exact SimpleGraph.ConnectedComponent.sound hconn
  have hx1arm : omega ∈ traceBoundaryConnectionEvent m x1 :=
    mem_traceBoundaryConnectionEvent_of_connected_outside hm (hA hx1A)
      (hB hy1B) hx1y1
  have hx2arm : omega ∈ traceBoundaryConnectionEvent m x2 :=
    mem_traceBoundaryConnectionEvent_of_connected_outside hm (hA hx2A)
      (hB hy2B) hx2y2
  rw [Set.mem_iUnion]
  refine ⟨x1, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hx1A, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨x2, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hx2A, ?_⟩
  rw [mem_twoArmDisconnectedTraceEvent]
  refine ⟨mem_traceBoundaryConnectionEvent.1 hx1arm,
    mem_traceBoundaryConnectionEvent.1 hx2arm, ?_⟩
  intro hbox
  exact hnotx hbox.2.2.connected

end StatMech.FrontierB
