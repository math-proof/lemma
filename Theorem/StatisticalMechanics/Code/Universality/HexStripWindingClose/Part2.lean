/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripWinding.Part7
import Structure.StatisticalMechanics.Code.Universality.HexStripWindingClose


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


namespace HexStripBand

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ} (B : HexStripBand inRegion a h0 z)


theorem windowField (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
    (k : ℕ) (hk : k ≤ ts.length) :
    B.w ≤ hexStripWinding_runningHead h0 ts k
      ∧ hexStripWinding_runningHead h0 ts k < B.w + 6 := by
  refine hexUmlauf_window_of_wall_noFullTurn a h0 ts B.w hadm.1
    (B.wall ts hadm) (B.noFullTurn ts hadm) ?_ k hk
  
  rw [hexStripWinding_runningHead_zero]; exact B.hh0U

end HexStripBand
end StatMech.Universality
