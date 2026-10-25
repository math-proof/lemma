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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part4
open Finset Matrix
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheEigenvalueCandidate {n : ℕ} (c : ℝ)
    (p : Fin n → ℝ) : ℂ :=
  (∏ j, sixVertexBetheL c (sixVertexBethePhase (p j))) +
    ∏ j, sixVertexBetheM c (sixVertexBethePhase (p j))


def sixVertexPairedRootFamily {k : ℕ} (p : Fin k → ℝ) :
    Fin (k + k) → ℝ :=
  fun i => match finSumFinEquiv.symm i with
    | Sum.inl j => p j
    | Sum.inr j => -p j

end
end StatMech.FrontierD
