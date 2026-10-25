/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part3
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


@[simp] theorem gridWalk_zero (g : ℕ → Site 2) :
    gridWalk g 0 = Walk.nil := rfl

@[simp] theorem gridWalk_succ (g : ℕ → Site 2) (n : ℕ) :
    gridWalk g (n + 1) =
      (gridWalk g n).append (gridConnector (g n) (g (n + 1))) := rfl


theorem gridWalk_mem_support_cases (g : ℕ → Site 2) (n : ℕ) (z : Site 2)
    (hz : z ∈ (gridWalk g n).support) :
    z = g 0 ∨ ∃ k < n, z ∈ (gridConnector (g k) (g (k + 1))).support := by
  induction n with
  | zero =>
      left
      simpa using hz
  | succ n ih =>
      rw [gridWalk_succ, Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · rcases ih hz with h | ⟨k, hk, hzk⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, hk.trans (Nat.lt_succ_self n), hzk⟩
      · exact Or.inr ⟨n, Nat.lt_succ_self n, hz⟩


end ContinuousRectangleCrossing
end StatMech
