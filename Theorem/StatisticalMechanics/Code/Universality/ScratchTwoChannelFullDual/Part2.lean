/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

@[simp] theorem rlc_twoChannelFullAmbientConfig_source {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    rlc_twoChannelFullAmbientConfig gamma gamma' omega
        (f.1.map Subtype.val) = omega f := by
  unfold rlc_twoChannelFullAmbientConfig
  split
  · rename_i hsource
    have heq : hsource.some =
        (⟨f, rfl⟩ : RlcTwoChannelAmbientSourceEdge gamma gamma'
          (f.1.map Subtype.val)) :=
      rlc_twoChannelAmbientSourceEdge_unique _ _
    rw [heq]
  · rename_i hsource
    exact False.elim (hsource ⟨⟨f, rfl⟩⟩)

theorem rlc_twoChannelFullAmbientConfig_trace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true := by
  unfold rlc_twoChannelFullAmbientConfig
  split
  · rename_i hsource
    obtain ⟨f⟩ := hsource
    exfalso
    induction hf : f.1.1 using Sym2.inductionOn with
    | _ x y =>
        have hfmem := f.1.2
        rw [hf, SimpleGraph.mem_edgeSet] at hfmem
        apply hfmem.2
        refine ⟨?_, ?_⟩
        · have hlat := hfmem.1.elim
            (fun h => h.1) (fun h => h.1)
          exact hlat
        · have heq : e = s((x : Site 2), (y : Site 2)) := by
            simpa [hf, Sym2.map_mk] using f.2.symm
          rw [heq] at he
          exact he
  · simp


end
end StatMech.Universality
