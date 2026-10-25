/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Mathlib.GroupTheory.Perm.Fin
import Def.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part2
open Finset Matrix
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheAmplitude_eq_source {n : ℕ} (c : ℝ)
    (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    sixVertexBetheAmplitude c p σ =
      (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
        ∏ k, ∏ l ∈ Finset.Ioi k,
          sixVertexBethePhase (p (σ k)) *
            (sixVertexBethePhase (-(p (σ k))) +
              sixVertexBethePhase (p (σ l)) - 2 * sixVertexDelta c) := by
  unfold sixVertexBetheAmplitude sixVertexBethePairProduct
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  apply Finset.prod_congr rfl
  intro l _
  exact sixVertexBethePairFactor_phase c (p (σ k)) (p (σ l))

theorem sixVertexBethePairProduct_ne_zero {c : ℝ} (hc : 2 < c)
    {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    sixVertexBethePairProduct c p σ ≠ 0 := by
  unfold sixVertexBethePairProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  apply Finset.prod_ne_zero_iff.mpr
  intro l _
  exact sixVertexBethePairFactor_phase_ne_zero hc _ _

theorem sixVertexBetheAmplitude_ne_zero {c : ℝ} (hc : 2 < c)
    {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    sixVertexBetheAmplitude c p σ ≠ 0 := by
  unfold sixVertexBetheAmplitude
  apply mul_ne_zero
  · norm_cast
    exact Units.ne_zero (Equiv.Perm.sign σ)
  · exact sixVertexBethePairProduct_ne_zero hc p σ


end
end StatMech.FrontierD
