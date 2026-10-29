/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.LastExit.Part2
import Def.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part3
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


variable {d : ℕ}


theorem mem_boxOffCEdges {C : Set (Site d)} {n : ℕ} {x z : Site d}
    (hx : x ∈ box d n) (hxC : x ∉ C) (hz : z ∈ box d n) (hzC : z ∉ C) :
    s(x, z) ∈ boxOffCEdges d C n := by
  classical
  unfold boxOffCEdges
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [mem_edgesWithinFinset]
    exact ⟨x, mem_boxFinsetOC.mpr hx, z, mem_boxFinsetOC.mpr hz, rfl⟩
  · intro w hw
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption


theorem agree_boxOffC {C : Set (Site d)} {n : ℕ} {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ (boxOffCEdges d C n : Set (Sym2 (Site d))), ω e = ω' e)
    {x z : Site d} (hx : x ∈ box d n \ C) (hz : z ∈ box d n \ C) :
    ω s(x, z) = ω' s(x, z) := by
  apply hagree
  rw [Finset.mem_coe]
  exact mem_boxOffCEdges hx.1 hx.2 hz.1 hz.2


theorem offClusterBoxCrossing_congr {C : Set (Site d)} {y : Site d} {n : ℕ}
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ (boxOffCEdges d C n : Set (Sym2 (Site d))), ω e = ω' e) :
    offClusterBoxCrossing d C y n ω ↔ offClusterBoxCrossing d C y n ω' := by
  have key : ∀ (η η' : ConfigSpace (Sym2 (Site d))),
      (∀ e ∈ (boxOffCEdges d C n : Set (Sym2 (Site d))), η e = η' e) →
      offClusterBoxCrossing d C y n η → offClusterBoxCrossing d C y n η' := by
    intro η η' hag hηcross
    obtain ⟨z, hzbox, hy, hz, hconn⟩ := hηcross
    refine ⟨z, hzbox, hy, hz, ?_⟩
    rw [← connWithinR_congr (box d n \ C) hy hz (fun x hx w hw => agree_boxOffC hag hx hw)]
    exact hconn
  exact ⟨key ω ω' hagree, key ω' ω (fun e he => (hagree e he).symm)⟩


theorem offClusterBoxCrossing_dependsOn (C : Set (Site d)) (y : Site d) (n : ℕ) :
    DependsOn ({ω | offClusterBoxCrossing d C y n ω}.indicator (fun _ => (1 : ℝ)))
      (boxOffCEdges d C n : Set (Sym2 (Site d))) := by
  intro ω ω' h
  have hiff : (ω ∈ {ω | offClusterBoxCrossing d C y n ω}) ↔
      (ω' ∈ {ω | offClusterBoxCrossing d C y n ω}) := by
    simp only [Set.mem_setOf_eq]
    exact offClusterBoxCrossing_congr (fun e he => h e he)
  by_cases hmem : ω ∈ {ω | offClusterBoxCrossing d C y n ω}
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hiff.mpr hc))]


theorem disjoint_boxOffC_incident (K S : Finset (Site d)) (n : ℕ) :
    Disjoint (boxOffCEdges d (K : Set (Site d)) n) (incidentWithinFinset K S) := by
  classical
  rw [Finset.disjoint_left]
  intro e he hinc
  unfold boxOffCEdges at he
  rw [Finset.mem_filter] at he
  obtain ⟨_, hnotinK⟩ := he
  rw [mem_incidentWithinFinset] at hinc
  obtain ⟨x, hxK, _, _, rfl⟩ := hinc
  exact hnotinK x (by rw [Sym2.mem_iff]; left; rfl) hxK


theorem boundaryEdge_notMem_boxOffC (K : Finset (Site d)) (x y : Site d) (n : ℕ)
    (hxK : x ∈ K) : s(x, y) ∉ boxOffCEdges d (K : Set (Site d)) n := by
  classical
  unfold boxOffCEdges
  rw [Finset.mem_filter]
  rintro ⟨_, hnotinK⟩
  exact hnotinK x (by rw [Sym2.mem_iff]; left; rfl) (by simpa using hxK)


theorem disjoint_boxOffC_incidentUnion (K S : Finset (Site d)) (x y : Site d) (n : ℕ)
    (hxK : x ∈ K) :
    Disjoint (incidentWithinFinset K S ∪ {s(x, y)}) (boxOffCEdges d (K : Set (Site d)) n) := by
  classical
  rw [Finset.disjoint_union_left]
  refine ⟨(disjoint_boxOffC_incident K S n).symm, ?_⟩
  rw [Finset.disjoint_singleton_left]
  exact boundaryEdge_notMem_boxOffC K x y n hxK


theorem dependsOn_inter {E : Type*} {A B : Set (ConfigSpace E)} {T U : Set E}
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) T)
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) U) :
    DependsOn ((A ∩ B).indicator (fun _ => (1 : ℝ))) (T ∪ U) := by
  have hrw : (A ∩ B).indicator (fun _ => (1 : ℝ))
      = fun ω => A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω; rw [← Set.inter_indicator_mul]; simp
  rw [hrw]
  intro ω ω' h
  simp only
  rw [hA (fun e he => h e (Or.inl he)), hB (fun e he => h e (Or.inr he))]


theorem offCluster_factor (p : NNReal) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (K : Finset (Site d)) (x y : Site d) (n : ℕ)
    (hxK : x ∈ K) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω})
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
            ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω} := by
  have hA : DependsOn ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
        ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}).indicator (fun _ => (1 : ℝ)))
      ((incidentWithinFinset K S : Set (Sym2 (Site d))) ∪ ({s(x, y)} : Set (Sym2 (Site d)))) :=
    dependsOn_inter (clusterEvent_dependsOn hoS) (boundaryOpen_dependsOn (K : Set (Site d)) x y)
  refine indep_cylinder_inf p hp _ _ (incidentWithinFinset K S ∪ {s(x, y)})
    (boxOffCEdges d (K : Set (Site d)) n) ?_ ?_ (offClusterBoxCrossing_dependsOn _ _ _)
  · exact disjoint_boxOffC_incidentUnion K S x y n hxK
  · rw [Finset.coe_union, Finset.coe_singleton]
    exact hA


theorem offClusterBox_subset_crossingFrom (C : Set (Site d)) (y : Site d) (n : ℕ) :
    {ω | offClusterBoxCrossing d C y n ω} ⊆ crossingEventFrom d y n := by
  intro ω hω
  obtain ⟨z, hzbox, _, _, hconn⟩ := hω
  exact ⟨z, hconn.connected, hzbox⟩


theorem offClusterBox_crossProb_le (p : NNReal) (hp : p ≤ 1) (C : Set (Site d)) (y : Site d)
    {L m n : ℕ} (hy : y ∈ box d L) (hmLn : m + L ≤ n) (hm : 1 ≤ m) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        {ω | offClusterBoxCrossing d C y n ω}
      ≤ crossProb d p hp m := by
  calc (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          {ω | offClusterBoxCrossing d C y n ω}
      ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (crossingEventFrom d y n) :=
        measureReal_mono (offClusterBox_subset_crossingFrom C y n)
    _ ≤ crossProb d p hp m := crossProbFrom_le p hp y hy hmLn hm


theorem crossingEvent_lastExit_boxsubset (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hSbox : (S : Set (Site d)) ⊆ box d (n - 1)) :
    crossingEvent d n ⊆
      ⋃ (K : Finset (Site d)), ⋃ (x : Site d), ⋃ (y : Site d),
        (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω}) := by
  intro ω hω
  obtain ⟨v, hconn, hv⟩ := hω
  set C := clusterWithin d ω (S : Set (Site d)) (origin d) with hC
  have hoC : origin d ∈ C := ⟨hoS, hoS, connectedWithin_refl ω _ ⟨origin d, hoS⟩⟩
  have hCsub : C ⊆ (S : Set (Site d)) := fun z hz => hz.1
  have hvC : v ∉ C := fun hvc => hv (hSbox (hCsub hvc))
  have hCfin : C.Finite := (S.finite_toSet).subset hCsub
  set K := hCfin.toFinset with hK
  have hKC : (K : Set (Site d)) = C := by simp [hK]
  obtain ⟨x, y, hx, hy, hopen, hwithin⟩ := lattice_lastExit ω C (origin d) v hoC hvC hconn
  have hxbox : x ∈ box d (n - 1) := hSbox (hCsub hx)
  have hadj : (hypercubicLattice d).Adj x y := hopen.1
  have hybox : y ∈ box d n := by
    have := adj_box_step hxbox hadj
    rwa [show n - 1 + 1 = n from by omega] at this
  obtain ⟨z, hz, _hzbox, hzconn⟩ := extract_box ω C y v n hn hy hvC hybox hv hwithin
  simp only [Set.mem_iUnion]
  refine ⟨K, x, y, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · show clusterWithin d ω (S : Set (Site d)) (origin d) = (K : Set (Site d))
    rw [hKC]
  · show boundaryOpen d (K : Set (Site d)) x y ω
    rw [hKC]; exact ⟨hx, hy, hopen⟩
  · show offClusterBoxCrossing d (K : Set (Site d)) y n ω
    rw [hKC]
    exact ⟨z, _hzbox, ⟨hybox, hy⟩, hz, hzconn⟩


end Percolation
end StatMech
