/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_insetLeftAttachedPath {n : Int} (gamma : RlcInsetLeftSourcePath n) :
    RlcLeftDiagonalPath n := by
  let x : leftSide (-2 * n) 0 (-n) n := ⟨gamma.1.1, by
    rw [mem_leftSide]
    have h:=gamma.1.1.2
    rw [mem_leftSide] at h
    exact ⟨by rw [mem_rect] at h ⊢; omega, h.2⟩⟩
  let y : rightSide (-2 * n) 0 (-n) n :=
    ⟨![0,(gamma.1.2.1:Site 2) 1], by
      rw [mem_rightSide, mem_rect]
      have h:=gamma.1.2.1.2
      rw [mem_rightSide, mem_rect] at h
      simp
      omega⟩
  let p0 := gamma.1.2.2.1.map (rlc_insetLeftHom n)
  let gx : rect (-2 * n) 0 (-n) n := ⟨gamma.1.1, by
    have h:=gamma.1.1.2
    rw [mem_leftSide, mem_rect] at h
    rw [mem_rect]
    omega⟩
  let gy : rect (-2 * n) 0 (-n) n := ⟨gamma.1.2.1, by
    have h:=gamma.1.2.1.2
    rw [mem_rightSide, mem_rect] at h
    rw [mem_rect]
    omega⟩
  let p : ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)).Walk gx gy :=
    p0.copy (by apply Subtype.ext; rfl) (by apply Subtype.ext; rfl)
  have hadj : ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)).Adj
      gy ⟨y, rightSide_subset y.2⟩ := by
    change (hypercubicLattice 2).Adj (gamma.1.2.1:Site 2)
      (![0,(gamma.1.2.1:Site 2) 1]:Site 2)
    have hx:=gamma.1.2.1.2.2
    simp [hypercubicLattice_adj, Fin.sum_univ_two, hx]
  let w := p.concat hadj
  have hp : p.IsPath := by
    simpa [p, SimpleGraph.Walk.isPath_copy] using
      gamma.1.2.2.1.map_isPath_of_injective (rlc_insetLeftHom_injective n) gamma.1.2.2.2
  have hyNot : (⟨y,rightSide_subset y.2⟩ : rect (-2 * n) 0 (-n) n)
      ∉ p.support := by
    intro hmem
    simp only [p, SimpleGraph.Walk.support_copy,p0,
      SimpleGraph.Walk.support_map,List.mem_map] at hmem
    obtain ⟨z,_hz,heq⟩:=hmem
    have heq0:=congrArg (fun u : rect (-2 * n) 0 (-n) n => (u:Site 2) 0) heq
    have hz0 : (z:Site 2) 0 ≤ -1 := by
      have hzmem:=z.2
      rw [mem_rect] at hzmem
      omega
    change (z:Site 2) 0 = 0 at heq0
    omega
  have hw : w.IsPath := hp.concat hyNot hadj
  refine ⟨⟨x,y,⟨w,hw⟩⟩,gamma.2.1,?_⟩
  change 0 ≤ (gamma.1.2.1:Site 2) 1
  exact le_of_lt gamma.2.2

noncomputable def rlc_insetLeftAttachmentEdge {n : Int} (gamma : RlcInsetLeftSourcePath n) : Sym2 (Site 2) :=
  s((gamma.1.2.1:Site 2), (![0,(gamma.1.2.1:Site 2) 1]:Site 2))

end
end StatMech.Universality
