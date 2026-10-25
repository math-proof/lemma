/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexSectorNoAdjacent {N n : Nat} (x : SixVertexSector N n) : Prop :=
  (∀ (k : Nat) (hk : k + 1 < n),
      (sixVertexSectorPosition x ⟨k, by omega⟩).val + 1 <
        (sixVertexSectorPosition x ⟨k + 1, hk⟩).val) ∧
    ∀ hn : 0 < n,
      (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val + 1 <
        N + (sixVertexSectorPosition x ⟨0, hn⟩).val

end
end StatMech.FrontierD
