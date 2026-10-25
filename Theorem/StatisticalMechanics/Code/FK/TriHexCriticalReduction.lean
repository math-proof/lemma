/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
import Def.StatisticalMechanics.Code.FK.TriHexCriticalReduction
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC FrontierA

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


theorem PeriodicGraph.measurableSet_openSubgraphAdj
    (P : PeriodicGraph V) (x y : V) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 V) | (P.openSubgraph omega).Adj x y} := by
  by_cases hxy : P.graph.Adj x y
  · have heq :
        {omega : ConfigSpace (Sym2 V) | (P.openSubgraph omega).Adj x y} =
          {omega | omega s(x, y) = true} := by
      ext omega
      rw [Set.mem_setOf_eq, P.openSubgraph_adj]
      exact ⟨fun h => h.2, fun h => ⟨hxy, h⟩⟩
    rw [heq]
    exact measurableSet_eq_fun
      (ConfigSpace.measurable_eval s(x, y)) measurable_const
  · have heq :
        {omega : ConfigSpace (Sym2 V) | (P.openSubgraph omega).Adj x y} = ∅ := by
      ext omega
      rw [Set.mem_setOf_eq, P.openSubgraph_adj]
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun h => hxy h.1
    rw [heq]
    exact MeasurableSet.empty

theorem PeriodicGraph.measurableSet_openChain
    (P : PeriodicGraph V) (l : List V) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 V) |
        List.IsChain (P.openSubgraph omega).Adj l} := by
  induction l with
  | nil => simp only [List.isChain_nil, Set.setOf_true, MeasurableSet.univ]
  | cons a l ih =>
      cases l with
      | nil => simp only [List.isChain_singleton, Set.setOf_true, MeasurableSet.univ]
      | cons b l =>
          have heq :
              {omega : ConfigSpace (Sym2 V) |
                  List.IsChain (P.openSubgraph omega).Adj (a :: b :: l)} =
                {omega | (P.openSubgraph omega).Adj a b} ∩
                  {omega | List.IsChain (P.openSubgraph omega).Adj (b :: l)} := by
            ext omega
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff,
              List.isChain_cons_cons]
          rw [heq]
          exact (P.measurableSet_openSubgraphAdj a b).inter ih

theorem PeriodicGraph.reachable_iff_openChain
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x y : V) :
    (P.openSubgraph omega).Reachable x y ↔
      ∃ l : List V, List.IsChain (P.openSubgraph omega).Adj (x :: l) ∧
        (x :: l).getLast (List.cons_ne_nil _ _) = y := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    obtain ⟨l, hchain, hlast⟩ :=
      List.exists_isChain_cons_of_relationReflTransGen h
    exact ⟨l, hchain, hlast⟩
  · rintro ⟨l, hchain, hlast⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hchain hlast


theorem PeriodicGraph.measurableSet_twoPointEvent
    [Countable V] (P : PeriodicGraph V) (x y : V) :
    MeasurableSet (P.twoPointEvent x y) := by
  classical
  have heq : P.twoPointEvent x y =
      ⋃ l : List V,
        ({omega | List.IsChain (P.openSubgraph omega).Adj (x :: l)} ∩
          if (x :: l).getLast (List.cons_ne_nil _ _) = y then Set.univ else ∅) := by
    ext omega
    rw [PeriodicGraph.twoPointEvent, Set.mem_setOf_eq,
      P.reachable_iff_openChain]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨l, hchain, hlast⟩
      exact ⟨l, hchain, by rw [if_pos hlast]; trivial⟩
    · rintro ⟨l, hchain, hlast⟩
      refine ⟨l, hchain, ?_⟩
      by_cases h : (x :: l).getLast (List.cons_ne_nil _ _) = y
      · exact h
      · rw [if_neg h] at hlast
        exact (Set.notMem_empty _ hlast).elim
  rw [heq]
  apply MeasurableSet.iUnion
  intro l
  apply MeasurableSet.inter (P.measurableSet_openChain (x :: l))
  split <;> simp


end PeriodicPlanar
end FK
end StatMech
