/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Def.StatisticalMechanics.Code.Lattice.EarContraction.Part3
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem mem_cutWitness (v : Site 2) :
    v ∈ cutWitness ↔ v = ![0, 0] ∨ v = ![1, 0] ∨ v = ![1, 1] ∨ v = ![2, 1] := by
  unfold cutWitness; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem cw_v00 : (![0, 0] : Site 2) ∈ cutWitness := by rw [mem_cutWitness]; tauto

theorem cw_v10 : (![1, 0] : Site 2) ∈ cutWitness := by rw [mem_cutWitness]; tauto

theorem cw_v11 : (![1, 1] : Site 2) ∈ cutWitness := by rw [mem_cutWitness]; tauto

theorem cw_v21 : (![2, 1] : Site 2) ∈ cutWitness := by rw [mem_cutWitness]; tauto


theorem cutWitness_cellConnected : CellConnected cutWitness := by
  rw [CellConnected, SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨![0, 0], cw_v00⟩⟩⟩
  have e1 : ((hypercubicLattice 2).induce cutWitness).Adj ⟨![0, 0], cw_v00⟩ ⟨![1, 0], cw_v10⟩ := by
    rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have e2 : ((hypercubicLattice 2).induce cutWitness).Adj ⟨![1, 0], cw_v10⟩ ⟨![1, 1], cw_v11⟩ := by
    rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have e3 : ((hypercubicLattice 2).induce cutWitness).Adj ⟨![1, 1], cw_v11⟩ ⟨![2, 1], cw_v21⟩ := by
    rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have r0 : ∀ x : ↑cutWitness,
      ((hypercubicLattice 2).induce cutWitness).Reachable ⟨![0, 0], cw_v00⟩ x := by
    rintro ⟨x, hx⟩
    rw [mem_cutWitness] at hx
    rcases hx with h | h | h | h <;> subst h
    · rfl
    · exact e1.reachable
    · exact e1.reachable.trans e2.reachable
    · exact (e1.reachable.trans e2.reachable).trans e3.reachable
  intro a b
  exact (r0 a).symm.trans (r0 b)


theorem cutWitness_extreme : IsExtremeCell cutWitness ![1, 1] := by
  refine ⟨cw_v11, ?_⟩
  intro v hv
  rw [mem_cutWitness] at hv
  unfold lexKey
  rcases hv with h | h | h | h <;> subst h <;> rw [Prod.Lex.toLex_le_toLex] <;> simp

theorem mem_cutWitness_diff (v : Site 2) :
    v ∈ cutWitness \ {![1, 1]} ↔ v = ![0, 0] ∨ v = ![1, 0] ∨ v = ![2, 1] := by
  rw [Set.mem_diff, mem_cutWitness, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, hne⟩
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd h hne
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h) <;> subst h <;>
      refine ⟨by tauto, fun hcon => ?_⟩ <;>
      · rw [funext_iff, Fin.forall_fin_two] at hcon; norm_num at hcon

theorem cwd_v21 : (![2, 1] : Site 2) ∈ cutWitness \ {![1, 1]} := by
  rw [mem_cutWitness_diff]; tauto

theorem cwd_v00 : (![0, 0] : Site 2) ∈ cutWitness \ {![1, 1]} := by
  rw [mem_cutWitness_diff]; tauto


theorem cwd_v21_isolated :
    ((hypercubicLattice 2).induce (cutWitness \ {![1, 1]})).neighborSet ⟨![2, 1], cwd_v21⟩ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨w, hw⟩ hadj
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj, hypercubicLattice_adj,
    Fin.sum_univ_two] at hadj
  rw [mem_cutWitness_diff] at hw
  rcases hw with h | h | h <;> subst h <;> simp at hadj

theorem cwd_v21_ne_v00 :
    (⟨![2, 1], cwd_v21⟩ : ↑(cutWitness \ {![1, 1]})) ≠ ⟨![0, 0], cwd_v00⟩ := by
  intro h
  have := congrFun (congrArg Subtype.val h) 0
  norm_num at this


theorem cutWitness_diff_not_cellConnected : ¬ CellConnected (cutWitness \ {![1, 1]}) := by
  intro h
  have hreach := h.preconnected ⟨![2, 1], cwd_v21⟩ ⟨![0, 0], cwd_v00⟩
  exact not_reachable_of_neighborSet_left_eq_empty cwd_v21_ne_v00 cwd_v21_isolated hreach


end Lattice
end StatMech
