/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWStrictAxisSourcePartition
import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_insetRightAttachedPath {n : Int}
    (gamma : RlcInsetRightSourcePath n) : RlcRightDiagonalPath n := by
  let x : leftSide 0 (2 * n) (-n) n :=
    ⟨![0, (gamma.1.1 : Site 2) 1], by
      rw [mem_leftSide, mem_rect]
      have h := gamma.1.1.2
      rw [mem_leftSide, mem_rect] at h
      simp
      omega⟩
  let y : rightSide 0 (2 * n) (-n) n := ⟨gamma.1.2.1, by
    rw [mem_rightSide]
    have h := gamma.1.2.1.2
    rw [mem_rightSide] at h
    exact ⟨by
      rw [mem_rect] at h ⊢
      omega, h.2⟩⟩
  let p0 := gamma.1.2.2.1.map (rlc_insetRightHom n)
  let gx : rect 0 (2 * n) (-n) n := ⟨gamma.1.1, by
    have h := gamma.1.1.2
    rw [mem_leftSide, mem_rect] at h
    rw [mem_rect]
    omega⟩
  let gy : rect 0 (2 * n) (-n) n := ⟨gamma.1.2.1, by
    have h := gamma.1.2.1.2
    rw [mem_rightSide, mem_rect] at h
    rw [mem_rect]
    omega⟩
  let p : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Walk gx gy :=
    p0.copy (by apply Subtype.ext; rfl) (by apply Subtype.ext; rfl)
  have hadj : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Adj
      ⟨x, leftSide_subset x.2⟩ gx := by
    change (hypercubicLattice 2).Adj
      (![0, (gamma.1.1 : Site 2) 1] : Site 2) (gamma.1.1 : Site 2)
    have hx := gamma.1.1.2.2
    simp [hypercubicLattice_adj, Fin.sum_univ_two, hx]
  let w := SimpleGraph.Walk.cons hadj p
  have hp : p.IsPath := by
    simpa [p, SimpleGraph.Walk.isPath_copy] using
      gamma.1.2.2.1.map_isPath_of_injective
        (rlc_insetRightHom_injective n) gamma.1.2.2.2
  have hxNot : (⟨x, leftSide_subset x.2⟩ :
      rect 0 (2 * n) (-n) n) ∉ p.support := by
    intro hmem
    simp only [p, SimpleGraph.Walk.support_copy, p0,
      SimpleGraph.Walk.support_map, List.mem_map] at hmem
    obtain ⟨z, _hz, heq⟩ := hmem
    have heq0 := congrArg
      (fun u : rect 0 (2 * n) (-n) n => (u : Site 2) 0) heq
    have hz0 : 1 ≤ (z : Site 2) 0 := by
      have hzmem := z.2
      rw [mem_rect] at hzmem
      omega
    change (z : Site 2) 0 = 0 at heq0
    omega
  have hw : w.IsPath := hp.cons hxNot
  refine ⟨⟨x, y, ⟨w, hw⟩⟩, ?_, gamma.2.2⟩
  change (gamma.1.1 : Site 2) 1 ≤ 0
  exact le_of_lt gamma.2.1


noncomputable def rlc_insetRightAttachmentEdge {n : Int}
    (gamma : RlcInsetRightSourcePath n) : Sym2 (Site 2) :=
  s((![0, (gamma.1.1 : Site 2) 1] : Site 2),
    (gamma.1.1 : Site 2))


end
end StatMech.Universality
