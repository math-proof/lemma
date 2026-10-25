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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part4
open Finset Matrix
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

theorem prod_sixVertexPairedRootFamily {k : ℕ} (p : Fin k → ℝ)
    (f : ℝ → ℂ) :
    (∏ i, f (sixVertexPairedRootFamily p i)) =
      (∏ j, f (p j)) * ∏ j, f (-p j) := by
  let g : Fin k ⊕ Fin k → ℂ := fun s => match s with
    | Sum.inl j => f (p j)
    | Sum.inr j => f (-p j)
  calc
    (∏ i, f (sixVertexPairedRootFamily p i)) = ∏ s, g s := by
      symm
      apply Fintype.prod_equiv finSumFinEquiv
      intro s
      change g s = f (sixVertexPairedRootFamily p (finSumFinEquiv s))
      unfold sixVertexPairedRootFamily
      rw [Equiv.symm_apply_apply]
      dsimp [g]
      cases s <;> rfl
    _ = (∏ j, f (p j)) * ∏ j, f (-p j) := by
      rw [Fintype.prod_sum_type]

theorem sixVertexBetheEigenvalueCandidate_paired {k : ℕ} (c : ℝ)
    (p : Fin k → ℝ) :
    sixVertexBetheEigenvalueCandidate c (sixVertexPairedRootFamily p) =
      sixVertexSymmetricBetheEigenvalueCandidate c p := by
  unfold sixVertexBetheEigenvalueCandidate
  unfold sixVertexSymmetricBetheEigenvalueCandidate
  rw [prod_sixVertexPairedRootFamily p
      (fun r => sixVertexBetheL c (sixVertexBethePhase r)),
    prod_sixVertexPairedRootFamily p
      (fun r => sixVertexBetheM c (sixVertexBethePhase r)),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]


end
end StatMech.FrontierD
