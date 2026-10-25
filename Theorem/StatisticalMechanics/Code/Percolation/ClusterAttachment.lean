/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem cla_walk_survival_force (ω : ConfigSpace (Sym2 (Site d))) (W : Finset (Sym2 (Site d)))
    {a x : Site d} (w : (openSubgraph d ω).Walk a x) (hw : (0 : Site d) ∉ w.support) :
    Connected d (removeSite 0 (forceOpenFinset W ω)) a x := by
  induction w with
  | nil => exact connected_rfl
  | @cons u v t hadj p ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    push Not at hw
    obtain ⟨h0u, h0rest⟩ := hw
    have hopen : IsOpenEdge d ω u v := hadj
    have h0v : (0 : Site d) ≠ v := fun h => h0rest (h ▸ p.start_mem_support)
    have h0e : (0 : Site d) ∉ s(u, v) := by
      simp only [Sym2.mem_iff]; push Not; exact ⟨fun h => h0u h, fun h => h0v h⟩
    have hsurv : IsOpenEdge d (removeSite 0 (forceOpenFinset W ω)) u v :=
      bka_isOpenEdge_survives ω W hopen h0e
    exact hsurv.connected.trans (ih h0rest)


theorem cla_walk_survival (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (w : (openSubgraph d ω).Walk a x) (hw : (0 : Site d) ∉ w.support) :
    Connected d (removeSite 0 ω) a x := by
  have h := cla_walk_survival_force ω ∅ w hw
  rwa [bka_forceOpenFinset_empty] at h


theorem cla_clusterAttachment_of_avoidingWalk (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hadj : (hypercubicLattice d).Adj 0 a) (hmem : a ∈ cluster d ω x)
    (w : (openSubgraph d ω).Walk a x) (hw : (0 : Site d) ∉ w.support)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    bma_ClusterAttachment ω x := by
  classical
  refine ⟨a, ∅, hadj, ?_, ?_, hmem, ?_, hri⟩
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · exact cla_walk_survival_force ω ∅ w hw


end Percolation
end StatMech
