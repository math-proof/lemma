/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAmplitudeExchange
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheWordAlgebra


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheIntMonomial {n : ℕ} (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → ℤ) : ℂ :=
  ∏ k, sixVertexBethePhase (p (σ k)) ^ (x k)


def sixVertexBetheShiftCoordinates {n : ℕ} (N : ℕ)
    (x : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  Fin.cases (x (Fin.last n) - N) fun i => x i.castSucc

end
end StatMech.FrontierD
