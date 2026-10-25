/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part6
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem eventually_wiredOpenExteriorFiniteMeasure_eq_wiredFiniteMeasure
    {d : Nat} {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : IsClopen A) :
    Filter.EventuallyEq atTop
      (fun k => ((wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq :
        ProbabilityMeasure _) : Measure _) A)
      (fun k => ((wiredFiniteMeasure d (phi k) hp hp1 hq :
        ProbabilityMeasure _) : Measure _) A) := by
  classical
  obtain ⟨F, hF⟩ := isClopen_dependsOn_finset A hA
  obtain ⟨N, t, ht⟩ := cdc_finset_in_box F
  filter_upwards [eventually_ge_atTop N] with k hk
  have hNphi : N ≤ phi k := hk.trans (hphi.id_le k)
  have hrange : ∀ e ∈ F, e ∈ Set.range (edgeIncl d (phi k)) := by
    intro e he
    rw [ht] at he
    obtain ⟨be, hbeMem, hbe⟩ := Finset.mem_image.mp he
    refine ⟨innerEdgeLE d hNphi be, ?_⟩
    rw [edgeIncl_innerEdgeLE, hbe]
  have hpre : extendWiredEdge d (phi k) ⁻¹' A =
      extendEdge d (phi k) ⁻¹' A := by
    ext omega
    exact hF _ _ (by
      intro e he
      obtain ⟨be, hbe⟩ := hrange e he
      rw [← hbe, extendWiredEdge_eq_of_range, extendEdge_eq_of_range])
  change Measure.map (extendWiredEdge d (phi k))
      (wiredFkPMF (boxGraph d (phi k)) (boxBoundary d (phi k))
        hp hp1 hq).toMeasure A =
    Measure.map (extendEdge d (phi k))
      (wiredFkPMF (boxGraph d (phi k)) (boxBoundary d (phi k))
        hp hp1 hq).toMeasure A
  rw [Measure.map_apply (measurable_extendWiredEdge d (phi k))
      hA.isOpen.measurableSet,
    Measure.map_apply (measurable_extendEdge d (phi k))
      hA.isOpen.measurableSet,
    hpre]

theorem tendsto_probabilityMeasure_of_eventuallyEq_on_clopen
    {E : Type*} [Countable E]
    (mu nu : Nat -> ProbabilityMeasure (ConfigSpace E))
    (limit : ProbabilityMeasure (ConfigSpace E))
    (hmu : Tendsto mu atTop (nhds limit))
    (heq : ∀ A : Set (ConfigSpace E), IsClopen A ->
      Filter.EventuallyEq atTop (fun n => nu n A) (fun n => mu n A)) :
    Tendsto nu atTop (nhds limit) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro xi hxi
  obtain ⟨psi, hpsi, hnu⟩ := hxi.tendsto_subseq
  apply ProbabilityMeasure.ext_of_forall_isClopen
  intro A hA
  have hxiA := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hnu hA
  have hlimitA := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (hmu.comp hpsi.tendsto_atTop) hA
  have heqSub := (heq A hA).comp_tendsto hpsi.tendsto_atTop
  exact tendsto_nhds_unique hxiA (hlimitA.congr' heqSub.symm)


theorem tendsto_wiredOpenExteriorFiniteMeasure
    {d : Nat} {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hclosed : Tendsto (fun k => wiredFiniteMeasure d (phi k) hp hp1 hq)
      atTop (nhds edgeLimit)) :
    Tendsto (fun k => wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq)
      atTop (nhds edgeLimit) := by
  apply tendsto_probabilityMeasure_of_eventuallyEq_on_clopen
    (fun k => wiredFiniteMeasure d (phi k) hp hp1 hq)
    (fun k => wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq)
    edgeLimit hclosed
  intro A hA
  have hmeasure := eventually_wiredOpenExteriorFiniteMeasure_eq_wiredFiniteMeasure
    hp hp1 hq phi hphi A hA
  filter_upwards [hmeasure] with k hk
  apply ENNReal.coe_injective
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hk

theorem exists_exterior_neighbor_of_boxBoundary
    {d n : Nat} (hn : 1 ≤ n) (y : boxVerts d n)
    (hy : boxBoundary d n y) :
    ∃ z : Site d, z ∈ exterior d n ∧
      (hypercubicLattice d).Adj (y : Site d) z := by
  rw [boxBoundary, mem_vertexBoundary] at hy
  simp only [mem_box, not_forall, not_le] at hy
  obtain ⟨i, hi⟩ := hy.2
  have habs : ((y : Site d) i).natAbs = n := by
    exact le_antisymm (hy.1 i) (by omega)
  by_cases hpos : 0 ≤ (y : Site d) i
  · let z : Site d := Function.update (y : Site d) i ((y : Site d) i + 1)
    refine ⟨z, ?_, ?_⟩
    · refine ⟨i, ?_⟩
      change n < (z i).natAbs
      simp only [z, Function.update_self]
      rw [
        Int.natAbs_add_of_nonneg hpos (by norm_num), habs]
      omega
    · rw [hypercubicLattice_adj]
      rw [Fintype.sum_eq_single i]
      · simp [z]
      · intro j hji
        simp [z, hji]
  · have hneg : (y : Site d) i < 0 := lt_of_not_ge hpos
    let z : Site d := Function.update (y : Site d) i ((y : Site d) i - 1)
    refine ⟨z, ?_, ?_⟩
    · refine ⟨i, ?_⟩
      change n < (z i).natAbs
      simp only [z, Function.update_self]
      rw [← Int.natAbs_neg]
      have hnonneg : 0 ≤ -((y : Site d) i) := by omega
      rw [show -((y : Site d) i - 1) = -((y : Site d) i) + 1 by ring,
        Int.natAbs_add_of_nonneg hnonneg (by norm_num), Int.natAbs_neg, habs]
      omega
    · rw [hypercubicLattice_adj]
      rw [Fintype.sum_eq_single i]
      · simp [z]
      · intro j hji
        simp [z, hji]

theorem exterior_adj_extendWiredEdge
    {d n : Nat} (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : exterior d n}
    (hxy : ((hypercubicLattice d).induce (exterior d n)).Adj x y) :
    (openSubgraph d (extendWiredEdge d n omega)).Adj (x : Site d) (y : Site d) := by
  rw [SimpleGraph.induce_adj] at hxy
  rw [openSubgraph_adj]
  refine ⟨hxy, ?_⟩
  apply extendWiredEdge_eq_true_of_not_range n omega
  intro hrange
  obtain ⟨be, hbe⟩ := hrange
  have hbeEdge : be ∈ (boxGraph d n).edgeFinset :=
    boxEdge_mem n be (x : Site d) (y : Site d) hxy hbe
  have himage : s((x : Site d), (y : Site d)) ∈
      Finset.image (edgeIncl d n) (boxGraph d n).edgeFinset :=
    Finset.mem_image.mpr ⟨be, hbeEdge, hbe⟩
  have hxbox := (IsingFK.hbx_mem_image_edgeIncl_iff d n
    (x : Site d) (y : Site d)).mp himage |>.1
  have hxnot : (x : Site d) ∉ box d n := by
    intro hx
    obtain ⟨i, hi⟩ := x.2
    exact (not_lt_of_ge (hx i)) hi
  exact hxnot hxbox

end StatMech.FK
