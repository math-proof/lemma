/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.InducedBC.Part11
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem psiEdgeFactor_pos {d n : ℕ} {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) : 0 < psiEdgeFactor d n ψ p := by
  unfold psiEdgeFactor
  apply Finset.prod_pos
  intro e _
  split
  · exact hp
  · linarith


theorem edgeProduct_psiExt (d n : ℕ) {p : ℝ} (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    edgeProduct (boxGraph d (n+1)) p (psiExt d n ψ ω)
      = edgeProduct (boxGraph d n) p ω * psiEdgeFactor d n ψ p := by
  classical
  unfold edgeProduct psiEdgeFactor
  rw [← Finset.prod_filter_mul_prod_filter_not (boxGraph d (n+1)).edgeFinset
    (fun e => e ∈ Set.range (innerEdge d n))]
  congr 1
  · 
    rw [← innerEdge_image_edgeFinset,
      Finset.prod_image (fun a _ b _ h => innerEdge_injective d n h)]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [psiExt_innerEdge]
  · 
    refine Finset.prod_congr rfl (fun e he => ?_)
    rw [Finset.mem_filter] at he
    rw [psiExt_eq_psi_of_not_range d n ψ ω he.2]


end FK
end StatMech
