/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorFamilies.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorDiagonal.Part2
open Finset
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


@[simp] theorem mem_finiteTreeDiagonalColorings
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (q : GrahamFourColoring ι) :
    q ∈ finiteTreeDiagonalColorings ends U i j k l ↔
      q.IsPartition U ∧
      sources ends q.color1 = {i, j} ∧
      sources ends q.color2 = ∅ ∧
      sources ends q.color3 = {k, l} ∧
      sources ends (q.color4 U) = ∅ ∧
      connK ends (q.color1 ∪ q.color3) i k := by
  simp [finiteTreeDiagonalColorings]


theorem grahamGlobalMiddleSwap_mem_diagonal_iff
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (q : GrahamFourColoring ι) :
    grahamGlobalMiddleSwap q ∈
        finiteTreeDiagonalColorings ends U i j k l ↔
      q ∈ finiteTreeMixedColorings ends U i j k l := by
  rw [mem_finiteTreeDiagonalColorings, mem_finiteTreeMixedColorings,
    grahamGlobalMiddleSwap_isPartition_iff,
    grahamGlobalMiddleSwap_color1,
    grahamGlobalMiddleSwap_color2,
    grahamGlobalMiddleSwap_color3,
    grahamGlobalMiddleSwap_color4]
  tauto


theorem finiteTreeMixedColorings_card_eq_diagonal
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V) :
    #(finiteTreeMixedColorings ends U i j k l) =
      #(finiteTreeDiagonalColorings ends U i j k l) := by
  apply Finset.card_bij (fun q _ => grahamGlobalMiddleSwap q)
  · intro q hq
    exact (grahamGlobalMiddleSwap_mem_diagonal_iff ends U i j k l q).2 hq
  · intro q hq r hr hqr
    simpa only [grahamGlobalMiddleSwap_involutive] using
      congrArg grahamGlobalMiddleSwap hqr
  · intro q hq
    refine ⟨grahamGlobalMiddleSwap q, ?_, ?_⟩
    · rw [← grahamGlobalMiddleSwap_mem_diagonal_iff ends U i j k l]
      simpa only [grahamGlobalMiddleSwap_involutive] using hq
    · exact grahamGlobalMiddleSwap_involutive q


end StatMech.FrontierA
