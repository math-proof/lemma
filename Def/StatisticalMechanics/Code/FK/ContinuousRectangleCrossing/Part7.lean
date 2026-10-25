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
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part6
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


def InRectangle (a b c d : ℝ) (p : Fin 2 → ℝ) : Prop :=
  a ≤ p 0 ∧ p 0 ≤ b ∧ c ≤ p 1 ∧ p 1 ≤ d


noncomputable def normalizeRectangle (a b c d : ℝ) (p : Fin 2 → ℝ) :
    Fin 2 → ℝ :=
  fun i => if i = 0 then (p 0 - a) / (b - a) else (p 1 - c) / (d - c)

end ContinuousRectangleCrossing
end StatMech
