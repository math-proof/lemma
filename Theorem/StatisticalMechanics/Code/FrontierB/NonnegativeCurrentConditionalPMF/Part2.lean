/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
import Def.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part2
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising


theorem summable_nonnegativeFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool) :
    Summable (nonnegativeFiniteParityKernel S lambda odd) := by
  let g : E → ℕ → ℝ := fun e k =>
    if he : e ∈ S then nonnegativeParityEdgeKernel (lambda e) (odd ⟨e, he⟩) k
    else nonnegativeParityEdgeKernel 0 false k
  have hg : ∀ e, Summable (g e) := by
    intro e
    unfold g
    split
    · rename_i he
      exact summable_nonnegativeParityEdgeKernel (hlambda ⟨e, he⟩) _
    · exact summable_nonnegativeParityEdgeKernel le_rfl _
  have hgnn : ∀ e k, 0 ≤ g e k := by
    intro e k
    unfold g
    split
    · rename_i he
      exact nonnegativeParityEdgeKernel_nonneg (hlambda ⟨e, he⟩) _ _
    · exact nonnegativeParityEdgeKernel_nonneg le_rfl _ _
  exact (prod_tsum_fubini g hg hgnn S).1.congr (fun a => by
    unfold nonnegativeFiniteParityKernel
    apply Fintype.prod_congr
    intro i
    simp [g])

theorem tsum_nonnegativeFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool) :
    ∑' a : ↑S → ℕ, nonnegativeFiniteParityKernel S lambda odd a = 1 := by
  let g : E → ℕ → ℝ := fun e k =>
    if he : e ∈ S then nonnegativeParityEdgeKernel (lambda e) (odd ⟨e, he⟩) k
    else nonnegativeParityEdgeKernel 0 false k
  have hg : ∀ e, Summable (g e) := by
    intro e
    unfold g
    split
    · rename_i he
      exact summable_nonnegativeParityEdgeKernel (hlambda ⟨e, he⟩) _
    · exact summable_nonnegativeParityEdgeKernel le_rfl _
  have hgnn : ∀ e k, 0 ≤ g e k := by
    intro e k
    unfold g
    split
    · rename_i he
      exact nonnegativeParityEdgeKernel_nonneg (hlambda ⟨e, he⟩) _ _
    · exact nonnegativeParityEdgeKernel_nonneg le_rfl _ _
  rw [show (∑' a : ↑S → ℕ,
      nonnegativeFiniteParityKernel S lambda odd a) =
      ∑' a : ↑S → ℕ, ∏ i : ↑S, g i.1 (a i) by
    apply tsum_congr
    intro a
    simp [nonnegativeFiniteParityKernel, g]]
  rw [← (prod_tsum_fubini g hg hgnn S).2]
  apply Finset.prod_eq_one
  intro e he
  simp only [g, dif_pos he]
  exact tsum_nonnegativeParityEdgeKernel (hlambda ⟨e, he⟩) (odd ⟨e, he⟩)

theorem tsum_ofReal_nonnegativeFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool) :
    ∑' a : ↑S → ℕ,
      ENNReal.ofReal (nonnegativeFiniteParityKernel S lambda odd a) = 1 := by
  have hnonneg : ∀ a : ↑S → ℕ,
      0 ≤ nonnegativeFiniteParityKernel S lambda odd a := by
    intro a
    exact Finset.prod_nonneg fun i _ =>
      nonnegativeParityEdgeKernel_nonneg (hlambda i) (odd i) (a i)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg
    (summable_nonnegativeFiniteParityKernel S lambda hlambda odd),
    tsum_nonnegativeFiniteParityKernel S lambda hlambda odd]
  simp


end StatMech.FrontierB
