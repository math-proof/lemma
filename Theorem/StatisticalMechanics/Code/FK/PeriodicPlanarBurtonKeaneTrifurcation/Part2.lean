/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part2
open Filter MeasureTheory Set SimpleGraph Topology Finset
open scoped ENNReal BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice StatMech.FrontierA

variable {V : Type*} [Countable V] [DecidableEq V]


theorem PeriodicGraph.measurableSet_openAdj
    (P : PeriodicGraph V) (x y : V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      (P.openSubgraph omega).Adj x y} := by
  by_cases hxy : P.graph.Adj x y
  · have heq : {omega : ConfigSpace (Sym2 V) |
        (P.openSubgraph omega).Adj x y} =
      {omega | omega s(x, y) = true} := by
      ext omega
      simp [P.openSubgraph_adj, hxy]
    rw [heq]
    exact measurableSet_eq_fun (ConfigSpace.measurable_eval s(x, y)) measurable_const
  · have heq : {omega : ConfigSpace (Sym2 V) |
        (P.openSubgraph omega).Adj x y} = ∅ := by
      ext omega
      simp [P.openSubgraph_adj, hxy]
    rw [heq]
    exact MeasurableSet.empty

theorem PeriodicGraph.measurableSet_isTrifurcation
    (P : PeriodicGraph V) (x : V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      P.IsTrifurcation omega x} := by
  have heq : {omega : ConfigSpace (Sym2 V) |
        P.IsTrifurcation omega x} =
      ⋃ a1, ⋃ a2, ⋃ a3,
        {omega | (P.openSubgraph omega).Adj x a1} ∩
        {omega | (P.openSubgraph omega).Adj x a2} ∩
        {omega | (P.openSubgraph omega).Adj x a3} ∩
        (removeVertex x ⁻¹'
          {eta | (P.cluster eta a1).Infinite}) ∩
        (removeVertex x ⁻¹'
          {eta | (P.cluster eta a2).Infinite}) ∩
        (removeVertex x ⁻¹'
          {eta | (P.cluster eta a3).Infinite}) ∩
        (removeVertex x ⁻¹' (P.twoPointEvent a1 a2))ᶜ ∩
        (removeVertex x ⁻¹' (P.twoPointEvent a1 a3))ᶜ ∩
        (removeVertex x ⁻¹' (P.twoPointEvent a2 a3))ᶜ := by
    ext omega
    simp [PeriodicGraph.IsTrifurcation, PeriodicGraph.twoPointEvent, and_assoc]
  rw [heq]
  refine MeasurableSet.iUnion fun a1 => MeasurableSet.iUnion fun a2 =>
    MeasurableSet.iUnion fun a3 => ?_
  exact ((((((((P.measurableSet_openAdj x a1).inter
    (P.measurableSet_openAdj x a2)).inter
    (P.measurableSet_openAdj x a3)).inter
    ((P.measurableSet_cluster_infinite a1).preimage (measurable_removeVertex x))).inter
    ((P.measurableSet_cluster_infinite a2).preimage (measurable_removeVertex x))).inter
    ((P.measurableSet_cluster_infinite a3).preimage (measurable_removeVertex x))).inter
    ((P.measurableSet_twoPointEvent a1 a2).preimage
      (measurable_removeVertex x)).compl).inter
    ((P.measurableSet_twoPointEvent a1 a3).preimage
      (measurable_removeVertex x)).compl).inter
    ((P.measurableSet_twoPointEvent a2 a3).preimage
      (measurable_removeVertex x)).compl

theorem PeriodicGraph.isTrifurcation_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    P.IsTrifurcation (P.configTranslate z omega) (P.shift z x) ↔
      P.IsTrifurcation omega x := by
  rw [PeriodicGraph.IsTrifurcation, PeriodicGraph.IsTrifurcation]
  constructor
  · rintro ⟨a1, a2, a3, h1, h2, h3, hi1, hi2, hi3, hd12, hd13, hd23⟩
    let b1 := P.shift (-z) a1
    let b2 := P.shift (-z) a2
    let b3 := P.shift (-z) a3
    refine ⟨b1, b2, b3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hm := (P.openSubgraphTranslateHom (-z)
        (P.configTranslate z omega)).map_rel h1
      simpa [b1] using hm
    · have hm := (P.openSubgraphTranslateHom (-z)
        (P.configTranslate z omega)).map_rel h2
      simpa [b2] using hm
    · have hm := (P.openSubgraphTranslateHom (-z)
        (P.configTranslate z omega)).map_rel h3
      simpa [b3] using hm
    · have hc := P.cluster_infinite_configTranslate z
        (removeVertex x omega) b1
      apply hc.mp
      rw [← P.removeVertex_configTranslate z omega x]
      simpa [b1] using hi1
    · have hc := P.cluster_infinite_configTranslate z
        (removeVertex x omega) b2
      apply hc.mp
      rw [← P.removeVertex_configTranslate z omega x]
      simpa [b2] using hi2
    · have hc := P.cluster_infinite_configTranslate z
        (removeVertex x omega) b3
      apply hc.mp
      rw [← P.removeVertex_configTranslate z omega x]
      simpa [b3] using hi3
    · intro hb
      apply hd12
      rw [P.removeVertex_configTranslate]
      simpa [b1, b2] using
        (P.reachable_configTranslate z (removeVertex x omega) b1 b2).mpr hb
    · intro hb
      apply hd13
      rw [P.removeVertex_configTranslate]
      simpa [b1, b3] using
        (P.reachable_configTranslate z (removeVertex x omega) b1 b3).mpr hb
    · intro hb
      apply hd23
      rw [P.removeVertex_configTranslate]
      simpa [b2, b3] using
        (P.reachable_configTranslate z (removeVertex x omega) b2 b3).mpr hb
  · rintro ⟨a1, a2, a3, h1, h2, h3, hi1, hi2, hi3, hd12, hd13, hd23⟩
    refine ⟨P.shift z a1, P.shift z a2, P.shift z a3,
      (P.openSubgraphTranslateHom z omega).map_rel h1,
      (P.openSubgraphTranslateHom z omega).map_rel h2,
      (P.openSubgraphTranslateHom z omega).map_rel h3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [P.removeVertex_configTranslate]
      exact (P.cluster_infinite_configTranslate z
        (removeVertex x omega) a1).mpr hi1
    · rw [P.removeVertex_configTranslate]
      exact (P.cluster_infinite_configTranslate z
        (removeVertex x omega) a2).mpr hi2
    · rw [P.removeVertex_configTranslate]
      exact (P.cluster_infinite_configTranslate z
        (removeVertex x omega) a3).mpr hi3
    · rw [P.removeVertex_configTranslate]
      intro h
      exact hd12 ((P.reachable_configTranslate z
        (removeVertex x omega) a1 a2).mp h)
    · rw [P.removeVertex_configTranslate]
      intro h
      exact hd13 ((P.reachable_configTranslate z
        (removeVertex x omega) a1 a3).mp h)
    · rw [P.removeVertex_configTranslate]
      intro h
      exact hd23 ((P.reachable_configTranslate z
        (removeVertex x omega) a2 a3).mp h)

theorem PeriodicGraph.trifurcation_measure_eq_orbit
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2) (u : V) :
    mu {omega | P.IsTrifurcation omega (P.shift z u)} =
      mu {omega | P.IsTrifurcation omega u} := by
  have hpre : P.configTranslate z ⁻¹'
      {omega | P.IsTrifurcation omega (P.shift z u)} =
      {omega | P.IsTrifurcation omega u} := by
    ext omega
    exact P.isTrifurcation_configTranslate z omega u
  calc
    mu {omega | P.IsTrifurcation omega (P.shift z u)} =
        mu (P.configTranslate z ⁻¹'
          {omega | P.IsTrifurcation omega (P.shift z u)}) :=
      ((hTI z).measure_preimage
        (P.measurableSet_isTrifurcation (P.shift z u)).nullMeasurableSet).symm
    _ = mu {omega | P.IsTrifurcation omega u} := by rw [hpre]


end StatMech.FK.PeriodicPlanar
