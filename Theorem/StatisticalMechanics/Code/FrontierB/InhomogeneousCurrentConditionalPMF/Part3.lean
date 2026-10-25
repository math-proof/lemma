/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Def.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part3
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness


section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem summable_inhomogeneousParityCurrentKernel
    (lambda : Sym2 V -> Real)
    (hlambda : forall e : G.edgeFinset, 0 < lambda e.1)
    (H : Finset (Sym2 V)) :
    Summable (inhomogeneousParityCurrentKernel G lambda H) := by
  let g : Sym2 V -> Nat -> Real := fun e k =>
    if he : e ∈ G.edgeFinset then
      parityEdgeKernel (lambda e) (e ∈ H) k
    else parityEdgeKernel 1 false k
  have hg : forall e, Summable (g e) := by
    intro e
    unfold g
    split <;> apply summable_parityEdgeKernel
  have hgnn : forall e k, 0 <= g e k := by
    intro e k
    unfold g
    split
    · rename_i he
      exact parityEdgeKernel_nonneg (lambda e) (hlambda ⟨e, he⟩) _ _
    · exact parityEdgeKernel_nonneg 1 (by norm_num) _ _
  exact (prod_tsum_fubini g hg hgnn G.edgeFinset).1.congr (fun m => by
    unfold inhomogeneousParityCurrentKernel
    apply Fintype.prod_congr
    intro e
    change g e.1 (m e) =
      parityEdgeKernel (lambda e.1) (e.1 ∈ H) (m e)
    dsimp only [g]
    rw [dif_pos e.2])

theorem tsum_inhomogeneousParityCurrentKernel
    (lambda : Sym2 V -> Real)
    (hlambda : forall e : G.edgeFinset, 0 < lambda e.1)
    (H : Finset (Sym2 V)) :
    ∑' m : EdgeCurrent G, inhomogeneousParityCurrentKernel G lambda H m = 1 := by
  let g : Sym2 V -> Nat -> Real := fun e k =>
    if he : e ∈ G.edgeFinset then
      parityEdgeKernel (lambda e) (e ∈ H) k
    else parityEdgeKernel 1 false k
  have hg : forall e, Summable (g e) := by
    intro e
    unfold g
    split <;> apply summable_parityEdgeKernel
  have hgnn : forall e k, 0 <= g e k := by
    intro e k
    unfold g
    split
    · rename_i he
      exact parityEdgeKernel_nonneg (lambda e) (hlambda ⟨e, he⟩) _ _
    · exact parityEdgeKernel_nonneg 1 (by norm_num) _ _
  rw [show (∑' m : EdgeCurrent G,
      inhomogeneousParityCurrentKernel G lambda H m) =
      ∑' m : EdgeCurrent G, ∏ e : G.edgeFinset, g e.1 (m e) by
    apply tsum_congr
    intro m
    unfold inhomogeneousParityCurrentKernel
    apply Fintype.prod_congr
    intro e
    change parityEdgeKernel (lambda e.1) (e.1 ∈ H) (m e) = g e.1 (m e)
    dsimp only [g]
    rw [dif_pos e.2]]
  rw [← (prod_tsum_fubini g hg hgnn G.edgeFinset).2]
  apply Finset.prod_eq_one
  intro e he
  simp only [g, dif_pos he]
  exact tsum_parityEdgeKernel (lambda e) (hlambda ⟨e, he⟩) (e ∈ H)

theorem tsum_ofReal_inhomogeneousParityCurrentKernel
    (lambda : Sym2 V -> Real)
    (hlambda : forall e : G.edgeFinset, 0 < lambda e.1)
    (H : Finset (Sym2 V)) :
    ∑' m : EdgeCurrent G,
      ENNReal.ofReal (inhomogeneousParityCurrentKernel G lambda H m) = 1 := by
  have hnonneg : forall m : EdgeCurrent G,
      0 <= inhomogeneousParityCurrentKernel G lambda H m := by
    intro m
    unfold inhomogeneousParityCurrentKernel
    exact Finset.prod_nonneg fun e _ =>
      parityEdgeKernel_nonneg (lambda e.1) (hlambda e) (e.1 ∈ H) (m e)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
    (summable_inhomogeneousParityCurrentKernel G lambda hlambda H),
    tsum_inhomogeneousParityCurrentKernel G lambda hlambda H]
  simp


end Graph
end StatMech.FrontierB
