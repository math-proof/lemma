/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Def.StatisticalMechanics.Code.Universality.HexInjections.Part2


namespace StatMech.Universality

open Complex

open scoped BigOperators


theorem hexColumnOfWidth_colSum (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (mem : List ℤ → Prop) (hreach hsummable hle_one) (y : ℝ) :
    (hexColumnOfWidth a h0 T χ mem hreach hsummable hle_one).colSum y
      = ∑' w : {ts // mem ts}, y ^ (HexWalk.ofTurns a h0 w.1).numVertices := rfl


end StatMech.Universality
