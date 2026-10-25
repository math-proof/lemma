/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part9
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem crossExt_eq_false_of_not_range (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {e : Sym2 (boxVerts d (n+1))} (he : e ∉ Set.range (innerEdge d n)) :
    crossExt d n ω e = false := by
  unfold crossExt; rw [dif_neg he]


theorem edgeProduct_crossExt (d n : ℕ) {p : ℝ} (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    edgeProduct (boxGraph d (n+1)) p (crossExt d n ω)
      = edgeProduct (boxGraph d n) p ω * (1 - p) ^ nonInnerEdgeCard d n := by
  classical
  unfold edgeProduct nonInnerEdgeCard
  rw [← Finset.prod_filter_mul_prod_filter_not (boxGraph d (n+1)).edgeFinset
    (fun e => e ∈ Set.range (innerEdge d n))]
  congr 1
  · 
    rw [← innerEdge_image_edgeFinset,
      Finset.prod_image (fun a _ b _ h => innerEdge_injective d n h)]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [crossExt_innerEdge]
  · 
    rw [Finset.prod_congr rfl (fun e he => ?_), Finset.prod_const]
    rw [Finset.mem_filter] at he
    rw [crossExt_eq_false_of_not_range d n ω he.2]
    rfl


end FK
end StatMech
