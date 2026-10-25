/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedTarget.Part3


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

theorem ons_prod_scaleEdgeWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (edge : Sym2 (ZMod L × ZMod L)) (t : ℂ)
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    (∏ f ∈ F, ons_scaleEdgeWeight weight edge t f) =
      if edge ∈ F then t * ∏ f ∈ F, weight f else ∏ f ∈ F, weight f := by
  classical
  induction F using Finset.induction with
  | empty => simp
  | @insert f F hf ih =>
      by_cases hfe : f = edge
      · subst f
        rw [Finset.prod_insert hf, Finset.prod_insert hf, ih]
        simp [ons_scaleEdgeWeight, hf]
        ring
      · rw [Finset.prod_insert hf, Finset.prod_insert hf, ih]
        have hef : edge ≠ f := Ne.symm hfe
        by_cases he : edge ∈ F
        · simp [ons_scaleEdgeWeight, hfe, hef, he]
          ring
        · simp [ons_scaleEdgeWeight, hfe, hef, he]

end StatMech.Onsager
