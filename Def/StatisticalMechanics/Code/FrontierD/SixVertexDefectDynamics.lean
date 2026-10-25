/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexDefectWeight {n : Nat} (d : Fin n → Nat) : Nat :=
  ∑ i, i.val * d i


def sixVertexDefectPile {n : Nat} (hn : 0 < n) (D : Nat) : Fin n → Nat :=
  fun i => if i.val = 0 then D else 0


def sixVertexDefectLower {n : Nat} (d : Fin n → Nat) (i : Fin n)
    (hi : 0 < i.val) : Fin n → Nat :=
  let p : Fin n := ⟨i.val - 1, by omega⟩
  Function.update (Function.update d i (d i - 1)) p (d p + 1)


def SixVertexDefectLowerStep {n : Nat} (d e : Fin n → Nat) : Prop :=
  ∃ (i : Fin n) (hi : 0 < i.val), 0 < d i ∧
    e = sixVertexDefectLower d i hi

end
end StatMech.FrontierD
