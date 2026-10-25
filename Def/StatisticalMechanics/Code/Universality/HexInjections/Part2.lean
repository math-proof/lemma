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
import Theorem.StatisticalMechanics.Code.Universality.HexInjections


namespace StatMech.Universality

open Complex

open scoped BigOperators


noncomputable def hexColumnOfWidth (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (mem : List ℤ → Prop)
    (hreach : ∀ ts, mem ts →
      ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re)
    (hsummable : Summable (fun w : {ts // mem ts} =>
      χ ^ (HexWalk.ofTurns a h0 w.1).numVertices))
    (hle_one : (∑' w : {ts // mem ts},
      χ ^ (HexWalk.ofTurns a h0 w.1).numVertices) ≤ 1) :
    HexColumn T χ where
  W := {ts : List ℤ // mem ts}
  len := fun w => (HexWalk.ofTurns a h0 w.1).numVertices
  len_ge := fun w => hexReachWidth_len_ge a h0 T w.1 (hreach w.1 w.2)
  crit_summable := hsummable
  crit_le_one := hle_one


end StatMech.Universality
