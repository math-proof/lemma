/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanCrossingCount.Part6
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem jcx_cross_A_adj (i j : Fin 7) : jcx_cross_A.Adj i j ↔ jcx_cross_A_rel i j := Iff.rfl


theorem jcx_cross_delete_eq_A :
    jcx_cross_G.deleteEdges jcx_cross_cycB.toSubgraph.edgeSet = jcx_cross_A := by
  ext i j
  rw [deleteEdges_adj, jcx_cross_cycB.edgeSet_toSubgraph, jcx_cross_A_adj, jcx_cross_G_adj]
  have hedges : ∀ e, e ∈ jcx_cross_cycB.edgeSet ↔
      e ∈ [s((2 : Fin 7), 4), s(4, 5), s(5, 6), s(6, 2)] := by
    intro e; rw [Walk.mem_edgeSet]
    have : jcx_cross_cycB.edges = [s((2 : Fin 7), 4), s(4, 5), s(5, 6), s(6, 2)] := by decide
    rw [this]
  rw [show (s(i, j) ∈ jcx_cross_cycB.edgeSet)
      = (s(i, j) ∈ [s((2 : Fin 7), 4), s(4, 5), s(5, 6), s(6, 2)]) from propext (hedges _)]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Sym2.eq_iff]
  revert i j; decide


theorem jcx_cross_cycB_iso : ∀ u ∈ jcx_cross_cycB.support, u ≠ 2 →
    ∀ w, ¬ (jcx_cross_G.deleteEdges jcx_cross_cycB.toSubgraph.edgeSet).Adj u w := by
  intro u hu hne w hadj
  rw [jcx_cross_delete_eq_A, jcx_cross_A_adj] at hadj
  have hsupp : jcx_cross_cycB.support = [2, 4, 5, 6, 2] := by decide
  rw [hsupp] at hu
  fin_cases hu <;> first
    | (exact hne rfl)
    | (revert hadj; fin_cases w <;> simp [jcx_cross_A_rel])


theorem jcx_cross_A_isCycles : jcx_cross_A.IsCycles := by
  intro v hv
  rw [Set.ncard_eq_two]
  fin_cases v
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jcx_cross_A_rel]⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jcx_cross_A_rel]⟩
  · exact ⟨1, 3, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jcx_cross_A_rel]⟩
  · exact ⟨0, 2, by decide,
      by ext j; fin_cases j <;> simp [SimpleGraph.mem_neighborSet, jcx_cross_A_rel]⟩
  · exfalso; obtain ⟨w, hw⟩ := hv; rw [SimpleGraph.mem_neighborSet, jcx_cross_A_adj] at hw
    revert hw; fin_cases w <;> simp [jcx_cross_A_rel]
  · exfalso; obtain ⟨w, hw⟩ := hv; rw [SimpleGraph.mem_neighborSet, jcx_cross_A_adj] at hw
    revert hw; fin_cases w <;> simp [jcx_cross_A_rel]
  · exfalso; obtain ⟨w, hw⟩ := hv; rw [SimpleGraph.mem_neighborSet, jcx_cross_A_adj] at hw
    revert hw; fin_cases w <;> simp [jcx_cross_A_rel]


theorem jcx_cross_isEvenPeelable : jcx_IsEvenPeelable jcx_cross_G := by
  refine jcx_IsEvenPeelable.cycle jcx_cross_isEven jcx_cross_cycB jcx_cross_cycB_isCycle
    jcx_cross_cycB_iso ?_
  rw [jcx_cross_delete_eq_A]
  exact jcx_isEvenPeelable_of_isCycles jcx_cross_A jcx_cross_A_isCycles


theorem jcx_faithfulDiscreteJordan_twoSquaresCorner :
    whc_FaithfulDiscreteJordan jcx_cross_P :=
  jcx_faithfulDiscreteJordan jcx_cross_P jcx_cross_isEvenPeelable


end Lattice
end StatMech
