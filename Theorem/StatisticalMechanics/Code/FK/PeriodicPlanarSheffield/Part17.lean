/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part17
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicGraph.measurableSet_openChain_sheffield
    (P : PeriodicGraph V) (l : List V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
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
                ({omega | P.graph.Adj a b} ∩
                  {omega | omega s(a, b) = true}) ∩
                {omega | List.IsChain (P.openSubgraph omega).Adj (b :: l)} := by
            ext omega
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff,
              List.isChain_cons_cons, P.openSubgraph_adj]
          rw [heq]
          apply MeasurableSet.inter
          · by_cases hab : P.graph.Adj a b
            · simpa [hab] using measurableSet_eq_fun
                (ConfigSpace.measurable_eval s(a, b)) measurable_const
            · simp [hab]
          · exact ih

theorem PeriodicGraph.reachable_iff_openChain_sheffield
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


end StatMech.FK.PeriodicPlanar
