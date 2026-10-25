/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryHolderAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
open Filter Set Topology Metric


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

theorem exists_bounded_anchor_of_average_normSq_le
    {ι : Type} (s : Finset ι) (hs : s.Nonempty) (f : ι → Complex)
    (E : Real) (hE : 0 ≤ E)
    (haverage : (∑ x ∈ s, Complex.normSq (f x)) ≤ (s.card : Real) * E) :
    ∃ x ∈ s, ‖f x‖ ≤ Real.sqrt E := by
  by_contra hnone
  push Not at hnone
  have hterm : ∀ x ∈ s, E < Complex.normSq (f x) := by
    intro x hx
    have hxlt := hnone x hx
    rw [Complex.normSq_eq_norm_sq]
    rw [← Real.sq_sqrt hE]
    exact (sq_lt_sq₀ (Real.sqrt_nonneg E) (norm_nonneg (f x))).2 hxlt
  have hstrict : (∑ _x ∈ s, E) < ∑ x ∈ s, Complex.normSq (f x) := by
    apply Finset.sum_lt_sum_of_nonempty hs
    intro x hx
    exact hterm x hx
  have hconst : (∑ _x ∈ s, E) = (s.card : Real) * E := by
    simp [nsmul_eq_mul]
  rw [hconst] at hstrict
  exact (not_lt_of_ge haverage) hstrict


theorem finiteWindow_average_normSq_le_of_embedding
    {α β : Type} [Fintype α] (window : α ↪ β)
    (concrete : α → Complex) (abstract : β → Complex) (E : Real)
    (hvalue : ∀ x, abstract (window x) = concrete x)
    (haverage : (∑ x, Complex.normSq (concrete x)) ≤
      (Fintype.card α : Real) * E) :
    (∑ y ∈ Finset.univ.map window, Complex.normSq (abstract y)) ≤
      ((Finset.univ.map window).card : Real) * E := by
  simpa [hvalue] using haverage

end
end StatMech.Universality
