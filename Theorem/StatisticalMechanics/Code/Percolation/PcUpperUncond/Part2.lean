/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpper.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Def.StatisticalMechanics.Code.Percolation.PcUpperUncond
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice


theorem closedCircuitEvent_eq_pi {u v : Site 2} (c : (hypercubicLattice 2).Walk u v) :
    closedCircuitEvent c
      = ((primalEdgeFinset c : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))).pi
          (fun _ => ({false} : Set Bool)) := by
  ext ω
  simp only [closedCircuitEvent, primalEdgeFinset, Set.mem_setOf_eq, Set.mem_pi,
    List.coe_toFinset, List.mem_map, Set.mem_singleton_iff,
    forall_exists_index, and_imp]
  constructor
  · rintro h e D hD rfl; exact h D hD
  · intro h D hD; exact h _ D hD rfl


theorem measure_closedCircuitEvent (p : NNReal) (hp : p ≤ 1) {u v : Site 2}
    (c : (hypercubicLattice 2).Walk u v) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedCircuitEvent c)
      = ((1 - p : NNReal) : ENNReal) ^ (primalEdgeFinset c).card := by
  rw [closedCircuitEvent_eq_pi, cylinder_all_closed]


theorem primalEdgeList_nodup {u : Site 2} (c : (hypercubicLattice 2).Walk u u)
    (hc : c.IsCycle) :
    (c.darts.map (fun D => sharedPrimalEdge D.fst D.snd)).Nodup := by
  have hed : c.edges.Nodup := hc.edges_nodup
  have hde : c.edges = c.darts.map (·.edge) := rfl
  have hdn : c.darts.Nodup := by rw [hde] at hed; exact hed.of_map _
  apply List.Nodup.map_on _ hdn
  intro D1 hD1 D2 hD2 heq
  have he : s(D1.fst, D1.snd) = s(D2.fst, D2.snd) :=
    sharedPrimalEdge_uncrossInj D1.adj D2.adj heq
  have hedm : (c.darts.map (·.edge)).Nodup := hde ▸ hed
  exact (List.inj_on_of_nodup_map hedm) hD1 hD2 he


theorem primalEdgeFinset_card_cycle {u : Site 2} (c : (hypercubicLattice 2).Walk u u)
    (hc : c.IsCycle) : (primalEdgeFinset c).card = c.length := by
  unfold primalEdgeFinset
  rw [List.toFinset_card_of_nodup (primalEdgeList_nodup c hc), List.length_map, c.length_darts]


theorem measure_closedCircuitEvent_cycle (p : NNReal) (hp : p ≤ 1) {u : Site 2}
    (c : (hypercubicLattice 2).Walk u u) (hc : c.IsCycle) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedCircuitEvent c)
      = ((1 - p : NNReal) : ENNReal) ^ c.length := by
  rw [measure_closedCircuitEvent p hp c, primalEdgeFinset_card_cycle c hc]


end Percolation
end StatMech
