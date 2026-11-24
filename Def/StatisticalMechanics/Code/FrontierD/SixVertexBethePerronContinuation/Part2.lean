module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation
open Finset Filter Matrix Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
