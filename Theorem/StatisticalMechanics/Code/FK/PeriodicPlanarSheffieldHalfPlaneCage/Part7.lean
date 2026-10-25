/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrosscut
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotated
import Mathlib.Topology.Subpath
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part6
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) :
    MeasurableSet (E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) := by
  classical
  have heq : E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R =
      ⋃ b : V, ⋃ (_hb : b ∈ E.lowerBoundaryRayVertices r c),
      ⋃ z : V, ⋃ (_hbz : P.graph.Adj b z),
      ⋃ (_hz : z ∉ E.rightHalfPlaneVertices r),
        {omega : ConfigSpace (Sym2 V) | omega s(b, z) = true} ∩
        ⋃ x : V, ⋃ (_hx : x ∈ L),
          {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} ∩
          P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∩
        ⋃ u : V, ⋃ (_hu : u ∈ E.upperBoundaryRayVertices r d),
        ⋃ w : V, ⋃ (_huw : P.graph.Adj u w),
        ⋃ (_hw : w ∉ E.rightHalfPlaneVertices r),
          {omega : ConfigSpace (Sym2 V) | omega s(u, w) = true} ∩
          ⋃ y : V, ⋃ (_hy : y ∈ R),
            {omega : ConfigSpace (Sym2 V) | (P.cluster omega y).Infinite} ∩
            P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∩
            P.connectedWithinSet
              (E.rightHalfPlaneStripVertices r n) x y := by
    ext omega
    constructor
    · rintro ⟨b, hb, z, hbz, hz, hbzOpen, x, hxL, hxInfinite, hxb,
        u, hu, w, huw, hw, huwOpen, y, hyR, hyInfinite, hyu, hxy⟩
      apply Set.mem_iUnion.2
      refine ⟨b, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hb, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨z, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hbz, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hz, hbzOpen, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨x, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hxL, ⟨hxInfinite, hxb⟩, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨u, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hu, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨w, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨huw, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨hw, huwOpen, ?_⟩
      apply Set.mem_iUnion.2
      refine ⟨y, ?_⟩
      apply Set.mem_iUnion.2
      exact ⟨hyR, ⟨hyInfinite, hyu⟩, hxy⟩
    · intro h
      obtain ⟨b, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hb, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨z, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hbz, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hz, hbzOpen, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨x, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hxL, ⟨hxInfinite, hxb⟩, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨u, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hu, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨w, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨huw, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hw, huwOpen, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨y, h⟩ := Set.mem_iUnion.1 h
      obtain ⟨hyR, ⟨hyInfinite, hyu⟩, hxy⟩ := Set.mem_iUnion.1 h
      exact ⟨b, hb, z, hbz, hz, hbzOpen, x, hxL, hxInfinite, hxb,
        u, hu, w, huw, hw, huwOpen, y, hyR, hyInfinite, hyu, hxy⟩
  rw [heq]
  exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _hb =>
    MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _hbz =>
    MeasurableSet.iUnion fun _hz =>
      (measurableSet_eq_fun (ConfigSpace.measurable_eval s(b, z))
        measurable_const).inter
      (MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
        ((P.measurableSet_cluster_infinite x).inter
          (P.connectedWithinSet_measurableSet
            (E.rightHalfPlaneVertices r) x b)).inter
        (MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun _hu =>
          MeasurableSet.iUnion fun w => MeasurableSet.iUnion fun _huw =>
          MeasurableSet.iUnion fun _hw =>
            (measurableSet_eq_fun (ConfigSpace.measurable_eval s(u, w))
              measurable_const).inter
            (MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
              ((P.measurableSet_cluster_infinite y).inter
                (P.connectedWithinSet_measurableSet
                  (E.rightHalfPlaneVertices r) y u)).inter
                (P.connectedWithinSet_measurableSet
                  (E.rightHalfPlaneStripVertices r n) x y))))

theorem PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_isIncreasing
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) :
    IsIncreasing (E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) := by
  intro omega eta homega
  rintro ⟨b, hb, z, hbz, hz, hbzOpen, x, hxL, hxInfinite, hxb,
    u, hu, w, huw, hw, huwOpen, y, hyR, hyInfinite, hyu, hxy⟩
  exact ⟨b, hb, z, hbz, hz, homega _ hbzOpen,
    x, hxL, P.clusterInfinite_isIncreasing x homega hxInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxb,
    u, hu, w, huw, hw, homega _ huwOpen,
    y, hyR, P.clusterInfinite_isIncreasing y homega hyInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ homega hyu,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxy⟩


theorem measureReal_pos_of_forceOpenFinset_preimage
    {X : Type*} [DecidableEq X] [Countable X]
    (mu : Measure (ConfigSpace (Sym2 X))) [IsFiniteMeasure mu]
    (hfe : HasFiniteEnergy mu) (F : Finset (Sym2 X))
    {A B : Set (ConfigSpace (Sym2 X))}
    (hB : MeasurableSet B) (hApos : 0 < mu.real A)
    (hsub : A ⊆ forceOpenFinset F ⁻¹' B) :
    0 < mu.real B := by
  by_contra hnot
  have hBreal : mu.real B = 0 :=
    le_antisymm (not_lt.mp hnot) measureReal_nonneg
  have hBzero : mu B = 0 :=
    ((ENNReal.toReal_eq_zero_iff (mu B)).mp hBreal).resolve_right
      (measure_ne_top mu _)
  have hmapZero := hfe F hBzero
  rw [Measure.map_apply (measurable_forceOpenFinset F) hB] at hmapZero
  have hAzero : mu A = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq hmapZero) bot_le
  unfold Measure.real at hApos
  rw [hAzero] at hApos
  norm_num at hApos


theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_forceOpen_subset_exited
    (E : PeriodicPlaneEmbedding P) {r c d : Real} {n : Nat}
    {L R : Finset V} {b u z w : V}
    (hbz : P.graph.Adj b z) (hz : z ∉ E.rightHalfPlaneVertices r)
    (huw : P.graph.Adj u w) (hw : w ∉ E.rightHalfPlaneVertices r) :
    E.finiteJoinedBoundaryArmAt r c d n L R b u ⊆
      forceOpenFinset {s(b, z), s(u, w)} ⁻¹'
        E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R := by
  intro omega homega
  rcases homega with ⟨hb, hu, x, hxL, hxInfinite, hxb,
    y, hyR, hyInfinite, hyu, hxy⟩
  let eta := forceOpenFinset {s(b, z), s(u, w)} omega
  have home : omega ≤ eta := by
    intro e
    by_cases he : e ∈ ({s(b, z), s(u, w)} : Finset (Sym2 V))
    · simp [eta, forceOpenFinset, he]
    · simp [eta, forceOpenFinset, he]
  change eta ∈ E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R
  refine ⟨b, hb, z, hbz, hz, ?_, x, hxL,
    P.clusterInfinite_isIncreasing x home hxInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ home hxb,
    u, hu, w, huw, hw, ?_, y, hyR,
    P.clusterInfinite_isIncreasing y home hyInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ home hyu,
    P.connectedWithinSet_isIncreasing _ _ _ home hxy⟩
  · simp [eta, forceOpenFinset]
  · simp [eta, forceOpenFinset]


theorem PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_measureReal_pos
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hfe : HasFiniteEnergy mu)
    (r c d : Real) (n : Nat) (L R : Finset V)
    (hpos : 0 < mu.real (E.finiteJoinedBoundaryArmEvent r c d n L R)) :
    0 < mu.real
      (E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) := by
  obtain ⟨b, u, hAtPos⟩ :=
    E.exists_positive_finiteJoinedBoundaryArmAt mu r c d n L R hpos
  have hAtNonempty :
      (E.finiteJoinedBoundaryArmAt r c d n L R b u).Nonempty := by
    by_contra hnot
    rw [Set.not_nonempty_iff_eq_empty.mp hnot] at hAtPos
    simp at hAtPos
  obtain ⟨omega, hb, hu, _⟩ := hAtNonempty
  obtain ⟨z, hbz, hz⟩ := hb.1.2
  obtain ⟨w, huw, hw⟩ := hu.1.2
  apply measureReal_pos_of_forceOpenFinset_preimage mu hfe
    {s(b, z), s(u, w)}
    (E.finiteOpenExitedJoinedBoundaryArmEvent_measurableSet r c d n L R)
    hAtPos
  exact E.finiteJoinedBoundaryArmAt_forceOpen_subset_exited
    hbz (by change ¬ r ≤ E.vertexCoord z 0; exact not_le.mpr hz)
    huw (by change ¬ r ≤ E.vertexCoord w 0; exact not_le.mpr hw)


theorem PeriodicPlaneEmbedding.exists_positive_finiteOpenExitedJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hfe : HasFiniteEnergy mu) (r : Real) :
    ∃ L U : Finset V, ∃ n : Nat,
      0 < mu.real
        (E.finiteOpenExitedJoinedBoundaryArmEvent r 0 1 n L U) := by
  obtain ⟨L, U, n, _hL, hjoined⟩ :=
    E.exists_highProbability_finiteJoinedBoundaryArmEvent_with_margin
      mu hFKG hTI hunique (r := r) (R := r) le_rfl
        (by norm_num : (0 : Real) < 1 / 2)
  refine ⟨L, U, n,
    E.finiteOpenExitedJoinedBoundaryArmEvent_measureReal_pos
      mu hfe r 0 1 n L U ?_⟩
  linarith


theorem PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent_openWalk
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r c d : Real} {n : Nat} {L R : Finset V}
    (h : omega ∈ E.finiteOpenExitedJoinedBoundaryArmEvent r c d n L R) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ z : V,
      z ∉ E.rightHalfPlaneVertices r ∧
    ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ w : V,
      w ∉ E.rightHalfPlaneVertices r ∧
    ∃ q : (P.openSubgraph omega).Walk z w,
      b ∈ q.support ∧ u ∈ q.support ∧
      ∀ v ∈ q.support, v = z ∨ v = w ∨
        v ∈ E.rightHalfPlaneVertices r := by
  rcases h with ⟨b, hb, z, hbz, hz, hbzOpen, x, _hxL, _hxInfinite, hxb,
    u, hu, w, huw, hw, huwOpen, y, _hyR, _hyInfinite, hyu, hxy⟩
  obtain ⟨qxb, hqxb⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxb
  obtain ⟨qyu, hqyu⟩ := P.connectedWithinSet_exists_openSubgraphWalk hyu
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  have hbzAdj : (P.openSubgraph omega).Adj b z := ⟨hbz, hbzOpen⟩
  have huwAdj : (P.openSubgraph omega).Adj u w := ⟨huw, huwOpen⟩
  let left : (P.openSubgraph omega).Walk z x := qxb.reverse.cons hbzAdj.symm
  let right : (P.openSubgraph omega).Walk y w :=
    qyu.append ((SimpleGraph.Walk.nil : (P.openSubgraph omega).Walk w w).cons huwAdj)
  let q : (P.openSubgraph omega).Walk z w := (left.append qxy).append right
  refine ⟨b, hb, z, hz, u, hu, w, hw, q, ?_, ?_, ?_⟩
  · have hbLeft : b ∈ left.support := by
      dsimp only [left]
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_reverse]
      apply List.mem_cons_of_mem
      simpa using qxb.end_mem_support
    simp only [q, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inl hbLeft)
  · have huRight : u ∈ right.support := by
      simp only [right, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl qyu.end_mem_support
    simp only [q, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr huRight
  · intro v hv
    simp only [q, SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with (hv | hv) | hv
    · dsimp only [left] at hv
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_reverse]
        at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hqxb v (by simpa using hv)))
    · exact Or.inr (Or.inr
        (E.rightHalfPlaneStripVertices_subset r n (hqxy v hv)))
    · simp only [right, SimpleGraph.Walk.mem_support_append_iff] at hv
      rcases hv with hv | hv
      · exact Or.inr (Or.inr (hqyu v hv))
      · rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hv
        simp only [List.mem_cons] at hv
        rcases hv with hv | hv
        · exact Or.inr (Or.inr (hv.symm ▸ hu.1.1))
        · have hvw : v = w := by simpa using hv
          exact Or.inr (Or.inl hvw)


end StatMech.FK.PeriodicPlanar
