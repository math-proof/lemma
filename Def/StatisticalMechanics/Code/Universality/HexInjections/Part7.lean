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
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part6


namespace StatMech.Universality

open Complex

open scoped BigOperators


noncomputable def hexHWCutPos (a : ℂ) (h0 : ℤ) (ts : List ℤ) : ℕ :=
  haveI : DecidableLT ℝ := Classical.decRel _
  match (HexWalk.ofTurns a h0 ts).vertices.argmax (fun v => v.re) with
  | none => 0
  | some v => (HexWalk.ofTurns a h0 ts).vertices.length -
      ((HexWalk.ofTurns a h0 ts).vertices.reverse.idxOf v + 1)


end StatMech.Universality
