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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part5
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexAlternatingEvenEmbedding
    {N n : Nat} (hhalf : 2 * n ≤ N) : Fin n ↪o Fin N := by
  let f : Fin n → Fin N := fun i =>
    ⟨2 * i.val, lt_of_lt_of_le (by omega) hhalf⟩
  exact OrderEmbedding.ofStrictMono f (by
    intro i j hij
    change 2 * i.val < 2 * j.val
    omega)

def sixVertexAlternatingOddEmbedding
    {N n : Nat} (hhalf : 2 * n ≤ N) : Fin n ↪o Fin N := by
  let f : Fin n → Fin N := fun i =>
    ⟨2 * i.val + 1, lt_of_lt_of_le (by omega) hhalf⟩
  exact OrderEmbedding.ofStrictMono f (by
    intro i j hij
    change 2 * i.val + 1 < 2 * j.val + 1
    omega)


def sixVertexAlternatingEvenSector
    (N n : Nat) (hhalf : 2 * n ≤ N) : SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv (sixVertexAlternatingEvenEmbedding hhalf)


def sixVertexAlternatingOddSector
    (N n : Nat) (hhalf : 2 * n ≤ N) : SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv (sixVertexAlternatingOddEmbedding hhalf)

end
end StatMech.FrontierD
