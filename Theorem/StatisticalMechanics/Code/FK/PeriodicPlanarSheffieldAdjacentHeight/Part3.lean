/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdjacentHeight.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

theorem sheffieldMacroArrayCoordinates_adjacent
    (B T : Nat) (a0 b0 c0 d0 : Nat → Real) (n k : Nat) :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    (q n (k + 1)).1 + 4 * B = (q n k).1 ∧
    (q n (k + 1)).2.1 - 4 * B = (q n k).2.1 ∧
    (q n (k + 1)).2.2.1 = (q n k).2.2.1 + 4 * B ∧
    (q n (k + 1)).2.2.2 =
      (q n k).2.2.2 - 4 * B + (T + 4 * B : Nat) := by
  dsimp only [sheffieldMacroArrayCoordinates]
  push_cast
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring


theorem sheffieldMacroArrayCoordinates_spans
    (B T : Nat) (hT : 8 * B < T)
    (a0 b0 c0 d0 : Nat → Real)
    (hspanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B) :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    (∀ n k, (q n k).1 + 5 * B < (q n k).2.1 - 5 * B) ∧
    ∀ n k, (q n k).2.2.1 + 5 * B < (q n k).2.2.2 - 5 * B := by
  dsimp only [sheffieldMacroArrayCoordinates]
  constructor
  · intro n k
    have h := hspanX0 n
    have hk : (0 : Real) ≤ k := by positivity
    have hBk : (0 : Real) ≤ (B : Real) * k := mul_nonneg (by positivity) hk
    push_cast at h ⊢
    nlinarith
  · intro n k
    have h := hspanY0 n
    have hTR : (8 : Real) * B < T := by exact_mod_cast hT
    have hk : (0 : Real) ≤ k := by positivity
    push_cast
    nlinarith [mul_nonneg (show (0 : Real) ≤ (T : Real) - 4 * B by
      linarith) hk]


end StatMech.FK.PeriodicPlanar
