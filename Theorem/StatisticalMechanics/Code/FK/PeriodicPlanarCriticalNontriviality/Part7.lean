/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part8
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


theorem isClopen_rootedOpenPathEvent
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] (u : V) (n : Nat) :
    IsClopen (rootedOpenPathEvent G u n) := by
  rw [rootedOpenPathEvent]
  apply isClopen_iUnion_of_finite
  intro c
  by_cases hc : (c.toWalk G).2.IsPath
  · rw [Set.iUnion_eq_if, if_pos hc]
    exact isClopen_walkOpenEvent _
  · rw [Set.iUnion_eq_if, if_neg hc]
    exact isClopen_empty

theorem isIncreasing_rootedOpenPathEvent
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] (u : V) (n : Nat) :
    IsIncreasing (rootedOpenPathEvent G u n) := by
  apply isUpperSet_iUnion₂
  intro c _
  exact isIncreasing_walkOpenEvent _

theorem PeriodicGraph.openSubgraph_le (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : P.openSubgraph omega ≤ P.graph := by
  intro x y hxy
  exact hxy.1

theorem PeriodicGraph.open_of_mem_walk_edges
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    {u v : V} (p : (P.openSubgraph omega).Walk u v)
    {e : Sym2 V} (he : e ∈ p.edges) : omega e = true := by
  have hedge := p.edges_subset_edgeSet he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, P.openSubgraph_adj] at hedge
      exact hedge.2


end StatMech.FK.PeriodicPlanar
