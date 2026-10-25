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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part5
open Finset Matrix
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexBethePairProduct_zero (c : ℝ)
    (p : Fin 0 → ℝ) (σ : Equiv.Perm (Fin 0)) :
    sixVertexBethePairProduct c p σ = 1 := by
  simp [sixVertexBethePairProduct]

@[simp] theorem sixVertexBetheAmplitude_zero (c : ℝ)
    (p : Fin 0 → ℝ) (σ : Equiv.Perm (Fin 0)) :
    sixVertexBetheAmplitude c p σ = 1 := by
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst σ
  simp [sixVertexBetheAmplitude]

@[simp] theorem sixVertexBetheEigenvalueCandidate_zero (c : ℝ)
    (p : Fin 0 → ℝ) : sixVertexBetheEigenvalueCandidate c p = 2 := by
  simp [sixVertexBetheEigenvalueCandidate]
  norm_num

theorem sixVertexCoordinateBetheEigenrelation_zero (N : ℕ) (c : ℝ)
    (p : Fin 0 → ℝ) :
    SixVertexCoordinateBetheEigenrelation (N := N) c p := by
  classical
  let emptySector : SixVertexSector N 0 := ⟨∅, by simp⟩
  letI : Unique (SixVertexSector N 0) := {
    default := emptySector
    uniq := fun y => by
      apply Subtype.ext
      exact Finset.card_eq_zero.mp y.prop }
  unfold SixVertexCoordinateBetheEigenrelation
  funext x
  rw [sixVertexSectorTransferComplex_mulVec_apply,
    Fintype.sum_subsingleton _ x]
  simp [sixVertexCoordinateBetheWave, sixVertexBetheMonomial,
    sixVertexBetheEigenvalueCandidate, sixVertexSectorTransfer,
    sixVertexTransfer]
  norm_num

end
end StatMech.FrontierD
