/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Def.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part4
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness


section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem inhomogeneousParityCurrentPMF_apply
    (lambda : Sym2 V -> Real)
    (hlambda : forall e : G.edgeFinset, 0 < lambda e.1)
    (H : Finset (Sym2 V)) (m : EdgeCurrent G) :
    inhomogeneousParityCurrentPMF G lambda hlambda H m =
      ENNReal.ofReal (inhomogeneousParityCurrentKernel G lambda H m) := by
  rw [inhomogeneousParityCurrentPMF, PMF.normalize_apply,
    tsum_ofReal_inhomogeneousParityCurrentKernel G lambda hlambda H]
  simp

theorem inhomogeneousParityCurrentKernel_eq_zero_of_support_ne
    (lambda : Sym2 V -> Real) (H : Finset (Sym2 V))
    (hH : H ⊆ G.edgeFinset) (m : EdgeCurrent G)
    (hm : currentParitySupport G m ≠ H) :
    inhomogeneousParityCurrentKernel G lambda H m = 0 := by
  have hall : ¬ (forall e : G.edgeFinset,
      if e.1 ∈ H then Odd (m e) else Even (m e)) :=
    fun h => hm ((currentParitySupport_eq_iff G H hH m).mpr h)
  push Not at hall
  obtain ⟨e, he⟩ := hall
  unfold inhomogeneousParityCurrentKernel
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  by_cases heH : e.1 ∈ H
  · have hnot : ¬ Odd (m e) := by simpa [heH] using he
    simp [parityEdgeKernel, heH, hnot]
  · have hnot : ¬ Even (m e) := by simpa [heH] using he
    simp [parityEdgeKernel, heH, hnot]


end Graph
end StatMech.FrontierB
