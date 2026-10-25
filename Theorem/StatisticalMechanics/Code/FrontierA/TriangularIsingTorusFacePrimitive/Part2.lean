/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhaseAssembly
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePrimitive
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

theorem triangularPositiveEdge_index_source
    (L : Nat) [Fact (2 < L)] (d : triangularTorusDart L) :
    triangularPositiveEdge L (triangularTorusPositiveIndex d.2)
        (triangularTorusPositiveSource d) =
      (triangularTorusDartEquiv L d).edge := by
  rcases d with ⟨⟨x, y⟩, a⟩
  fin_cases a <;>
    simp [triangularTorusPositiveIndex, triangularTorusPositiveSource,
      triangularPositiveEdge, triangularTorusPositiveDirection,
      triangularTorusDartEquiv_apply, triangularTorusDartToGraphDart,
      triangularTorusDirectionStep, SimpleGraph.Dart.edge, Sym2.eq_swap]

theorem triangularTorusCycle_positiveRepresentation_injective
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    Function.Injective (fun k : Fin p.darts.length =>
      triangularTorusPositiveRepresentation
        (triangularTorusCycleNativeDart L p k)) := by
  intro i j hij
  apply triangularTorusCycle_edge_injective L p hp
  change (kwGraphCycleDartLoop p i).edge =
    (kwGraphCycleDartLoop p j).edge
  rw [← triangularTorusCycleNativeDart_equiv L p i,
    ← triangularTorusCycleNativeDart_equiv L p j,
    ← triangularPositiveEdge_index_source L
      (triangularTorusCycleNativeDart L p i),
    ← triangularPositiveEdge_index_source L
      (triangularTorusCycleNativeDart L p j)]
  simpa [triangularTorusPositiveRepresentation] using congrArg
    (fun q : Fin 3 × (ZMod L × ZMod L) =>
      triangularPositiveEdge L q.1 q.2) hij

theorem triangularBoundaryCoeff_mul_step_fst
    {L : Nat} (lower upper : (ZMod L × ZMod L) → ZMod 2)
    (d : triangularTorusDart L) :
    triangularFaceBoundaryCoeff lower upper d * (triangularIntStep d.2).1 =
      triangularFacePositiveCoeff lower upper
          (triangularTorusPositiveIndex d.2)
          (triangularTorusPositiveSource d) *
        (triangularIntStep
          (triangularTorusPositiveDirection
            (triangularTorusPositiveIndex d.2))).1 := by
  rcases d with ⟨⟨x, y⟩, a⟩
  fin_cases a <;>
    simp [triangularFaceBoundaryCoeff, triangularFacePositiveCoeff,
      triangularTorusPositiveIndex, triangularTorusPositiveSource,
      triangularTorusPositiveDirection, triangularIntStep] <;> ring

theorem triangularBoundaryCoeff_mul_step_snd
    {L : Nat} (lower upper : (ZMod L × ZMod L) → ZMod 2)
    (d : triangularTorusDart L) :
    triangularFaceBoundaryCoeff lower upper d * (triangularIntStep d.2).2 =
      triangularFacePositiveCoeff lower upper
          (triangularTorusPositiveIndex d.2)
          (triangularTorusPositiveSource d) *
        (triangularIntStep
          (triangularTorusPositiveDirection
            (triangularTorusPositiveIndex d.2))).2 := by
  rcases d with ⟨⟨x, y⟩, a⟩
  fin_cases a <;>
    simp [triangularFaceBoundaryCoeff, triangularFacePositiveCoeff,
      triangularTorusPositiveIndex, triangularTorusPositiveSource,
      triangularTorusPositiveDirection, triangularIntStep] <;> ring

theorem triangularFacePositiveCoeff_full_fst_sum_eq_zero
    {L : Nat} [NeZero L]
    (lower upper : (ZMod L × ZMod L) → ZMod 2) :
    (∑ q : Fin 3 × (ZMod L × ZMod L),
      triangularFacePositiveCoeff lower upper q.1 q.2 *
        (triangularIntStep
          (triangularTorusPositiveDirection q.1)).1) = 0 := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  simp [triangularFacePositiveCoeff,
    triangularTorusPositiveDirection, triangularIntStep]
  rw [← Finset.sum_add_distrib, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro x _
  exact triangularFaceBoundary_horizontal_seam_sum lower upper x

theorem triangularFacePositiveCoeff_full_snd_sum_eq_zero
    {L : Nat} [NeZero L]
    (lower upper : (ZMod L × ZMod L) → ZMod 2) :
    (∑ q : Fin 3 × (ZMod L × ZMod L),
      triangularFacePositiveCoeff lower upper q.1 q.2 *
        (triangularIntStep
          (triangularTorusPositiveDirection q.1)).2) = 0 := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  simp [triangularFacePositiveCoeff,
    triangularTorusPositiveDirection, triangularIntStep]
  rw [← Finset.sum_add_distrib, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y _
  exact triangularFaceBoundary_vertical_seam_sum lower upper y

theorem triangularZeroHomology_cycleBoundaryCoeff_mul_step_fst_sum_eq_zero
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L p.edges.toFinset)
        (triangularZeroHomologyUpperPotential L p.edges.toFinset)
        (triangularTorusCycleNativeDart L p k) *
      (triangularIntStep
        (triangularTorusCycleNativeDart L p k).2).1) = 0 := by
  classical
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let F := p.edges.toFinset
  let lower := triangularZeroHomologyLowerPotential L F
  let upper := triangularZeroHomologyUpperPotential L F
  let d : Fin p.darts.length → triangularTorusDart L :=
    triangularTorusCycleNativeDart L p
  let rep : Fin p.darts.length → Fin 3 × (ZMod L × ZMod L) :=
    fun k => triangularTorusPositiveRepresentation (d k)
  let T := (Finset.univ : Finset (Fin 3 × (ZMod L × ZMod L))).filter
    (fun q => triangularPositiveEdge L q.1 q.2 ∈ F)
  let g : Fin 3 × (ZMod L × ZMod L) → Int := fun q =>
    triangularFacePositiveCoeff lower upper q.1 q.2 *
      (triangularIntStep (triangularTorusPositiveDirection q.1)).1
  have hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L) :=
    ons_cycle_edges_evenSubgraph (triangularTorusGraph L) p hp
  have hedge (k : Fin p.darts.length) :
      triangularPositiveEdge L (rep k).1 (rep k).2 =
        (kwGraphCycleDartLoop p k).edge := by
    rw [show rep k = triangularTorusPositiveRepresentation (d k) by rfl]
    rw [triangularTorusPositiveRepresentation,
      triangularPositiveEdge_index_source,
      triangularTorusCycleNativeDart_equiv]
  have hedgeMem (k : Fin p.darts.length) :
      (kwGraphCycleDartLoop p k).edge ∈ F := by
    rw [show F = p.edges.toFinset by rfl,
      triangularTorusCycle_edges_toFinset_eq_image L p,
      Finset.mem_image]
    exact ⟨k, Finset.mem_univ _, rfl⟩
  calc
    (∑ k, triangularFaceBoundaryCoeff lower upper (d k) *
        (triangularIntStep (d k).2).1) = ∑ q ∈ T, g q := by
      apply Finset.sum_bij (fun k _ => rep k)
      · intro k _
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [hedge k]; exact hedgeMem k⟩
      · intro i _ j _ hij
        exact triangularTorusCycle_positiveRepresentation_injective
          L p hp hij
      · intro q hq
        have hqF := (Finset.mem_filter.mp hq).2
        rw [show F = p.edges.toFinset by rfl,
          triangularTorusCycle_edges_toFinset_eq_image L p,
          Finset.mem_image] at hqF
        obtain ⟨k, hk, hedgeq⟩ := hqF
        have hpositive : triangularPositiveEdge L (rep k).1 (rep k).2 =
            triangularPositiveEdge L q.1 q.2 :=
          (hedge k).trans hedgeq
        have hpair := (triangularTorusPositiveEdge_eq_iff
          L (rep k).2 q.2 (rep k).1 q.1).mp hpositive
        exact ⟨k, hk, Prod.ext hpair.2 hpair.1⟩
      · intro k _
        exact triangularBoundaryCoeff_mul_step_fst lower upper (d k)
    _ = ∑ q : Fin 3 × (ZMod L × ZMod L), g q := by
      apply Finset.sum_subset
      · simp [T]
      · intro q _ hqT
        have hnotF : triangularPositiveEdge L q.1 q.2 ∉ F := by
          intro hmem
          apply hqT
          simp [T, hmem]
        have hz := triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem
          L F hF hhom
          (q.2, triangularTorusPositiveDirection q.1) (by
            simpa [triangularPositiveEdge] using hnotF)
        have hpc : triangularFacePositiveCoeff lower upper q.1 q.2 = 0 := by
          rcases q with ⟨a, q⟩
          fin_cases a <;>
            simpa [triangularFacePositiveCoeff,
              triangularFaceBoundaryCoeff,
              triangularTorusPositiveDirection] using hz
        change g q = 0
        simp [g, hpc]
    _ = 0 := triangularFacePositiveCoeff_full_fst_sum_eq_zero lower upper

theorem triangularZeroHomology_cycleBoundaryCoeff_mul_step_snd_sum_eq_zero
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L p.edges.toFinset)
        (triangularZeroHomologyUpperPotential L p.edges.toFinset)
        (triangularTorusCycleNativeDart L p k) *
      (triangularIntStep
        (triangularTorusCycleNativeDart L p k).2).2) = 0 := by
  classical
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let F := p.edges.toFinset
  let lower := triangularZeroHomologyLowerPotential L F
  let upper := triangularZeroHomologyUpperPotential L F
  let d : Fin p.darts.length → triangularTorusDart L :=
    triangularTorusCycleNativeDart L p
  let rep : Fin p.darts.length → Fin 3 × (ZMod L × ZMod L) :=
    fun k => triangularTorusPositiveRepresentation (d k)
  let T := (Finset.univ : Finset (Fin 3 × (ZMod L × ZMod L))).filter
    (fun q => triangularPositiveEdge L q.1 q.2 ∈ F)
  let g : Fin 3 × (ZMod L × ZMod L) → Int := fun q =>
    triangularFacePositiveCoeff lower upper q.1 q.2 *
      (triangularIntStep (triangularTorusPositiveDirection q.1)).2
  have hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L) :=
    ons_cycle_edges_evenSubgraph (triangularTorusGraph L) p hp
  have hedge (k : Fin p.darts.length) :
      triangularPositiveEdge L (rep k).1 (rep k).2 =
        (kwGraphCycleDartLoop p k).edge := by
    rw [show rep k = triangularTorusPositiveRepresentation (d k) by rfl]
    rw [triangularTorusPositiveRepresentation,
      triangularPositiveEdge_index_source,
      triangularTorusCycleNativeDart_equiv]
  have hedgeMem (k : Fin p.darts.length) :
      (kwGraphCycleDartLoop p k).edge ∈ F := by
    rw [show F = p.edges.toFinset by rfl,
      triangularTorusCycle_edges_toFinset_eq_image L p,
      Finset.mem_image]
    exact ⟨k, Finset.mem_univ _, rfl⟩
  calc
    (∑ k, triangularFaceBoundaryCoeff lower upper (d k) *
        (triangularIntStep (d k).2).2) = ∑ q ∈ T, g q := by
      apply Finset.sum_bij (fun k _ => rep k)
      · intro k _
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [hedge k]; exact hedgeMem k⟩
      · intro i _ j _ hij
        exact triangularTorusCycle_positiveRepresentation_injective
          L p hp hij
      · intro q hq
        have hqF := (Finset.mem_filter.mp hq).2
        rw [show F = p.edges.toFinset by rfl,
          triangularTorusCycle_edges_toFinset_eq_image L p,
          Finset.mem_image] at hqF
        obtain ⟨k, hk, hedgeq⟩ := hqF
        have hpositive : triangularPositiveEdge L (rep k).1 (rep k).2 =
            triangularPositiveEdge L q.1 q.2 :=
          (hedge k).trans hedgeq
        have hpair := (triangularTorusPositiveEdge_eq_iff
          L (rep k).2 q.2 (rep k).1 q.1).mp hpositive
        exact ⟨k, hk, Prod.ext hpair.2 hpair.1⟩
      · intro k _
        exact triangularBoundaryCoeff_mul_step_snd lower upper (d k)
    _ = ∑ q : Fin 3 × (ZMod L × ZMod L), g q := by
      apply Finset.sum_subset
      · simp [T]
      · intro q _ hqT
        have hnotF : triangularPositiveEdge L q.1 q.2 ∉ F := by
          intro hmem
          apply hqT
          simp [T, hmem]
        have hz := triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem
          L F hF hhom
          (q.2, triangularTorusPositiveDirection q.1) (by
            simpa [triangularPositiveEdge] using hnotF)
        have hpc : triangularFacePositiveCoeff lower upper q.1 q.2 = 0 := by
          rcases q with ⟨a, q⟩
          fin_cases a <;>
            simpa [triangularFacePositiveCoeff,
              triangularFaceBoundaryCoeff,
              triangularTorusPositiveDirection] using hz
        change g q = 0
        simp [g, hpc]
    _ = 0 := triangularFacePositiveCoeff_full_snd_sum_eq_zero lower upper

theorem triangularTorus_simpleCycle_zeroEvenHomology_displacement_eq_zero
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, triangularIntStep
      (triangularTorusCycleNativeDart L p k).2) = 0 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let lower := triangularZeroHomologyLowerPotential L p.edges.toFinset
  let upper := triangularZeroHomologyUpperPotential L p.edges.toFinset
  let d : Fin p.darts.length → triangularTorusDart L :=
    triangularTorusCycleNativeDart L p
  let C := triangularFaceBoundaryCoeff lower upper (d 0)
  have hconst : ∀ k, triangularFaceBoundaryCoeff lower upper (d k) = C := by
    exact triangularZeroHomology_cycleBoundaryCoeff_eq_root L p hp hhom
  have hC : C ≠ 0 := by
    exact triangularZeroHomology_cycleBoundaryCoeff_root_ne_zero
      L p hp hhom
  have hxWeighted :=
    triangularZeroHomology_cycleBoundaryCoeff_mul_step_fst_sum_eq_zero
      L p hp hhom
  have hyWeighted :=
    triangularZeroHomology_cycleBoundaryCoeff_mul_step_snd_sum_eq_zero
      L p hp hhom
  have hx : (∑ k, (triangularIntStep (d k).2).1) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hC
    calc
      C * ∑ k, (triangularIntStep (d k).2).1 =
          ∑ k, C * (triangularIntStep (d k).2).1 := by
        rw [Finset.mul_sum]
      _ = ∑ k, triangularFaceBoundaryCoeff lower upper (d k) *
          (triangularIntStep (d k).2).1 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hconst k]
      _ = 0 := hxWeighted
  have hy : (∑ k, (triangularIntStep (d k).2).2) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hC
    calc
      C * ∑ k, (triangularIntStep (d k).2).2 =
          ∑ k, C * (triangularIntStep (d k).2).2 := by
        rw [Finset.mul_sum]
      _ = ∑ k, triangularFaceBoundaryCoeff lower upper (d k) *
          (triangularIntStep (d k).2).2 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hconst k]
      _ = 0 := hyWeighted
  apply Prod.ext
  · simpa only [Prod.fst_sum, Prod.fst_zero] using hx
  · simpa only [Prod.snd_sum, Prod.snd_zero] using hy

theorem triangularTorus_zeroHomologyWinding
    (L : Nat) [Fact (2 < L)] : TriangularTorusZeroHomologyWinding L := by
  intro root p hp hsurface
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hhom := triangularTorusEvenHomology_eq_zero_of_surfaceHomology
    L p.edges.toFinset hsurface
  simpa only [triangularTorusCycleNativeDart_snd] using
    (triangularTorus_simpleCycle_zeroEvenHomology_displacement_eq_zero
      L p hp hhom)

theorem triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign_closed
    (L : Nat) [Fact (2 < L)]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
        (kwGraphCycleDartLoop p) =
      -(surfaceParitySign
        (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0)
          (surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
            p.edges.toFinset)) : Complex) := by
  exact triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign
    L rho hrho (triangularTorus_zeroHomologyWinding L) p hp

end StatMech.FrontierA
