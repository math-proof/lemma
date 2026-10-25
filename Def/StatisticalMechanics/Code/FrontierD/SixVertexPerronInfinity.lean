/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part7
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronInfinity
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexNoAdjacentInfinityTopIndex
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Fin (Fintype.card (SixVertexNoAdjacentSector N n)) := by
  letI : Nonempty (SixVertexNoAdjacentSector N n) :=
    ⟨sixVertexNoAdjacentAlternatingEven N n hn hhalf⟩
  exact ⟨0, Fintype.card_pos⟩

noncomputable def sixVertexNoAdjacentInfinityTopEigenvalue
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) : Real :=
  (sixVertexNoAdjacentTransferInfinity_isHermitian N n).eigenvalues₀
    (sixVertexNoAdjacentInfinityTopIndex N n hn hhalf)

end
end StatMech.FrontierD
