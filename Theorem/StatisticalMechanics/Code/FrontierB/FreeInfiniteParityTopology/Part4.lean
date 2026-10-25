/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityNoEscape.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorReduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FrontierB.FreeInfiniteParityTopology.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

theorem isOpen_connectivityStableNeighborhood_of_not_mem_frontier
    (omega : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d)) :
    IsOpen (connectivityStableNeighborhood omega A) := by
  classical
  unfold connectivityStableNeighborhood
  apply isOpen_biInter_finset
  intro x hx
  apply isOpen_biInter_finset
  intro y hy
  split_ifs with hxy
  · exact isOpen_connectedEvent x y
  · exact isOpen_interior

theorem mem_connectivityStableNeighborhood
    (omega : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d))
    (hfront : ∀ x ∈ A, ∀ y ∈ A,
      omega ∉ frontier {eta : ConfigSpace (Sym2 (Site d)) |
        Lattice.Connected d eta x y}) :
    omega ∈ connectivityStableNeighborhood omega A := by
  classical
  unfold connectivityStableNeighborhood
  simp only [Set.mem_iInter]
  intro x hx y hy
  split_ifs with hxy
  · exact hxy
  · have hnot := hfront x hx y hy
    rw [← Set.mem_compl_iff, compl_frontier_eq_union_interior] at hnot
    rcases hnot with hint | hint
    · have hc : Lattice.Connected d omega x y := by
        have hm : omega ∈ {eta : ConfigSpace (Sym2 (Site d)) |
            Lattice.Connected d eta x y} :=
          (show interior {eta : ConfigSpace (Sym2 (Site d)) |
              Lattice.Connected d eta x y} ⊆
            {eta | Lattice.Connected d eta x y} from interior_subset) hint
        exact hm
      exact absurd hc hxy
    · exact hint

theorem connectivityStableNeighborhood_connectivity
    (omega eta : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d))
    (heta : eta ∈ connectivityStableNeighborhood omega A)
    {x y : Site d} (hx : x ∈ A) (hy : y ∈ A) :
    Connected d omega x y ↔ Connected d eta x y := by
  classical
  unfold connectivityStableNeighborhood at heta
  simp only [Set.mem_iInter] at heta
  have h := heta x hx y hy
  split_ifs at h with hxy
  · exact ⟨fun _ => h, fun _ => hxy⟩
  · exact ⟨fun hc => absurd hc hxy,
      fun hc => False.elim ((interior_subset h) hc)⟩


theorem frontier_allClustersEvenEvent_subset_atLeastTwoInfinite
    (A : Finset (Site d)) :
    frontier (allClustersEvenEvent (hypercubicLattice d) A) ⊆
      atLeastTwoInfinite d := by
  classical
  intro omega homega
  by_contra hnotmulti
  have hpairfront : ∀ x ∈ A, ∀ y ∈ A,
      omega ∉ frontier {eta : ConfigSpace (Sym2 (Site d)) |
        Connected d eta x y} := by
    intro x hx y hy hfront
    exact hnotmulti (distinctInfiniteClusterEvent_subset_atLeastTwoInfinite x y
      (frontier_connectedEvent_subset_distinctInfiniteClusterEvent x y hfront))
  let U := connectivityStableNeighborhood omega A
  have hUopen : IsOpen U :=
    isOpen_connectivityStableNeighborhood_of_not_mem_frontier omega A
  have homegaU : omega ∈ U :=
    mem_connectivityStableNeighborhood omega A hpairfront
  have hstable : ∀ eta ∈ U,
      AllClustersEven (hypercubicLattice d) omega A ↔
        AllClustersEven (hypercubicLattice d) eta A := by
    intro eta heta
    apply allClustersEven_congr_of_mark_connectivity
    intro x hx y hy
    simpa only [openSub, openSubgraph, FK.Connected] using
      connectivityStableNeighborhood_connectivity omega eta A heta hx hy
  by_cases heven : AllClustersEven (hypercubicLattice d) omega A
  · apply homega.2
    apply mem_interior_iff_mem_nhds.2
    exact mem_of_superset (hUopen.mem_nhds homegaU) fun eta heta =>
      (hstable eta heta).1 heven
  · have hcompl : omega ∈ interior
        (allClustersEvenEvent (hypercubicLattice d) A)ᶜ := by
      apply mem_interior_iff_mem_nhds.2
      apply mem_of_superset (hUopen.mem_nhds homegaU)
      intro eta heta
      exact fun hetaEven => heven ((hstable eta heta).2 hetaEven)
    have hnotclosure : omega ∉ closure
        (allClustersEvenEvent (hypercubicLattice d) A) := by
      rw [← Set.mem_compl_iff, ← interior_compl]
      exact hcompl
    exact hnotclosure homega.1


theorem measure_frontier_allClustersEvenEvent_eq_zero
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0)
    (A : Finset (Site d)) :
    (mu : Measure _) (frontier
      (allClustersEvenEvent (hypercubicLattice d) A)) = 0 :=
  measure_mono_null (frontier_allClustersEvenEvent_subset_atLeastTwoInfinite A)
    hunique

theorem measurable_markReachableCount_lattice
    (A : Finset (Site d)) (x : Site d) :
    Measurable (fun omega : ConfigSpace (Sym2 (Site d)) =>
      markReachableCount (hypercubicLattice d) omega A x) := by
  classical
  have heq : (fun omega : ConfigSpace (Sym2 (Site d)) =>
      markReachableCount (hypercubicLattice d) omega A x) =
      fun omega => ∑ y ∈ A,
        {eta : ConfigSpace (Sym2 (Site d)) |
          Lattice.Connected d eta x y}.indicator (fun _ => (1 : Nat)) omega := by
    funext omega
    simp only [markReachableCount, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hxy : Lattice.Connected d omega x y
    · have hxy' : (openSub (hypercubicLattice d) omega).Reachable x y := hxy
      simp [hxy, hxy']
    · have hxy' : ¬(openSub (hypercubicLattice d) omega).Reachable x y := hxy
      simp [hxy, hxy']
  rw [heq]
  apply Finset.measurable_sum
  intro y hy
  exact measurable_const.indicator (measurableSet_connected x y)

theorem measurableSet_allClustersEvenEvent (A : Finset (Site d)) :
    MeasurableSet (allClustersEvenEvent (hypercubicLattice d) A) := by
  classical
  have heq : allClustersEvenEvent (hypercubicLattice d) A =
      ⋂ x ∈ A, (fun omega : ConfigSpace (Sym2 (Site d)) =>
        markReachableCount (hypercubicLattice d) omega A x) ⁻¹'
          {n : Nat | Even n} := by
    ext omega
    simp only [allClustersEvenEvent, Set.mem_iInter, Set.mem_preimage,
      Set.mem_setOf_eq]
    exact allClustersEven_iff_mark_reachability (hypercubicLattice d) omega A
  rw [heq]
  apply Finset.measurableSet_biInter
  intro x hx
  exact MeasurableSet.preimage MeasurableSet.of_discrete
    (measurable_markReachableCount_lattice A x)

theorem WeakConvergesTo.tendsto_real_of_null_frontier
    {E : Type*} [Countable E]
    {mu : Nat → ProbabilityMeasure (ConfigSpace E)}
    {nu : ProbabilityMeasure (ConfigSpace E)}
    (h : WeakConvergesTo mu nu) {A : Set (ConfigSpace E)}
    (hA : (nu : Measure _) (frontier A) = 0) :
    Tendsto (fun n => (mu n : Measure _).real A) atTop
      (nhds ((nu : Measure _).real A)) := by
  have hnn : Tendsto (fun n => mu n A) atTop (nhds (nu A)) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto h
      (by
        have hz : (↑(nu (frontier A)) : ENNReal) = 0 := by
          rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
          exact hA
        exact ENNReal.coe_eq_zero.1 hz)
  have hcoe := (NNReal.continuous_coe.tendsto _).comp hnn
  simpa only [Function.comp_def, ProbabilityMeasure.coe_apply_eq_real] using hcoe

end StatMech.FrontierB
