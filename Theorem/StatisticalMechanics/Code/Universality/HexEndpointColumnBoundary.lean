/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointColumnBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexHammersleyWelshClose.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

theorem hecb_endpoint_finset_bound
    {W : Type*} (f : W → ℝ)
    (hnn : ∀ w, 0 ≤ f w)
    (strip : Finset W → Finset W)
    (hsub : ∀ s, s ⊆ strip s)
    (lam tau : Finset W → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (htau : ∀ s, 0 ≤ tau s)
    (hbdry : ∀ s,
      hexCl * lam s + hexCt * tau s + ∑ w ∈ strip s, f w = 1) :
    ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1 :=
  hhw_finsetBound_of_singleStrip f hexCl hexCt
    (le_of_lt hexCl_pos) (le_of_lt hexCt_pos)
    hnn strip hsub lam tau hlam htau hbdry


end
end StatMech.Universality
