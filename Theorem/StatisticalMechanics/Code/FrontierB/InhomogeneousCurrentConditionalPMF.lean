/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Def.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness


theorem summable_inhomogeneousFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool) :
    Summable (inhomogeneousFiniteParityKernel S lambda odd) := by
  let g : E -> Nat -> Real := fun e k =>
    if he : e ∈ S then parityEdgeKernel (lambda e) (odd ⟨e, he⟩) k
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
  exact (prod_tsum_fubini g hg hgnn S).1.congr (fun a => by
    unfold inhomogeneousFiniteParityKernel
    apply Fintype.prod_congr
    intro i
    simp [g])

theorem tsum_inhomogeneousFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool) :
    ∑' a : S -> Nat, inhomogeneousFiniteParityKernel S lambda odd a = 1 := by
  let g : E -> Nat -> Real := fun e k =>
    if he : e ∈ S then parityEdgeKernel (lambda e) (odd ⟨e, he⟩) k
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
  rw [show (∑' a : S -> Nat,
      inhomogeneousFiniteParityKernel S lambda odd a) =
      ∑' a : S -> Nat, ∏ i : S, g i.1 (a i) by
    apply tsum_congr
    intro a
    simp [inhomogeneousFiniteParityKernel, g]]
  rw [← (prod_tsum_fubini g hg hgnn S).2]
  apply Finset.prod_eq_one
  intro e he
  simp only [g, dif_pos he]
  exact tsum_parityEdgeKernel (lambda e) (hlambda ⟨e, he⟩)
    (odd ⟨e, he⟩)

theorem tsum_ofReal_inhomogeneousFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (hlambda : forall e : S, 0 < lambda e.1) (odd : S -> Bool) :
    ∑' a : S -> Nat,
      ENNReal.ofReal (inhomogeneousFiniteParityKernel S lambda odd a) = 1 := by
  have hnonneg : forall a : S -> Nat,
      0 <= inhomogeneousFiniteParityKernel S lambda odd a := by
    intro a
    exact Finset.prod_nonneg fun i _ =>
      parityEdgeKernel_nonneg (lambda i.1) (hlambda i) (odd i) (a i)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
    (summable_inhomogeneousFiniteParityKernel S lambda hlambda odd),
    tsum_inhomogeneousFiniteParityKernel S lambda hlambda odd]
  simp


end StatMech.FrontierB
