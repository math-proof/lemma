/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexConnFinal
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2


namespace StatMech.Universality

open Complex HexWalk Filter Topology

open scoped Topology Real BigOperators


noncomputable def hexClosed_cw (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (x : ℝ) (ts : List ℤ) : ℝ :=
  haveI := Classical.propDecidable ((ofTurns a h0 ts).IsLegalSAW
      ∧ (ofTurns a h0 ts).StaysIn inRegion ∧ (ofTurns a h0 ts).EndsAt z)
  if (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z then x ^ (ofTurns a h0 ts).numVertices else 0


noncomputable def hexClosed_countObs (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (x : ℝ) : ℝ :=
  ∑' ts, hexClosed_cw inRegion a h0 z x ts


end StatMech.Universality
