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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part2
open Finset Matrix
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

def sixVertexBethePairProduct {n : ℕ} (c : ℝ) (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  ∏ k, ∏ l ∈ Finset.Ioi k,
    sixVertexBethePairFactor c (sixVertexBethePhase (p (σ k)))
      (sixVertexBethePhase (p (σ l)))


def sixVertexBetheAmplitude {n : ℕ} (c : ℝ) (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
    sixVertexBethePairProduct c p σ

end
end StatMech.FrontierD
