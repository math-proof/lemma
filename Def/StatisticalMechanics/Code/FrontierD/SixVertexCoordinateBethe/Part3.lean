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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part3
open Finset Matrix
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheMonomial {N n : ℕ} (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (x : SixVertexSector N n) : ℂ :=
  ∏ k, (sixVertexBethePhase (p (σ k))) ^
    (sixVertexSectorPosition x k).val


def sixVertexCoordinateBetheWave {N n : ℕ} (c : ℝ) (p : Fin n → ℝ) :
    SixVertexSector N n → ℂ :=
  fun x => ∑ σ : Equiv.Perm (Fin n),
    sixVertexBetheAmplitude c p σ * sixVertexBetheMonomial p σ x


def sixVertexSectorTransferComplex (N n : ℕ) (c : ℝ) :
    Matrix (SixVertexSector N n) (SixVertexSector N n) ℂ :=
  (sixVertexSectorTransfer N n c).map (fun r => (r : ℂ))

end
end StatMech.FrontierD
