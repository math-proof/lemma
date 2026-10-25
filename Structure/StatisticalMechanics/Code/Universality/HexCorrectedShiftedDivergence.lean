/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedShiftedDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedTopWitness.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

structure HexAsymmetricHighestCut (K : ℝ) where
  D : Type
  B₁ : Type
  B₂ : Type
  wtγ : D → ℝ
  wtB₁ : B₁ → ℝ
  wtB₂ : B₂ → ℝ
  wtγ_nn : ∀ d, 0 ≤ wtγ d
  wtB₁_nn : ∀ b, 0 ≤ wtB₁ b
  wtB₂_nn : ∀ b, 0 ≤ wtB₂ b
  split : D → B₁ × B₂
  split_injective : Function.Injective split
  weight_bound : ∀ d,
    wtγ d ≤ K * (wtB₁ (split d).1 * wtB₂ (split d).2)
  D_summable : Summable wtγ
  B₁_summable : Summable wtB₁
  B₂_summable : Summable wtB₂

end
end StatMech.Universality
