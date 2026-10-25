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
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part8
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


def clampX (a b : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then clampCoord a b (p 0) else p 1


def clampY (c d : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 1 then clampCoord c d (p 1) else p 0

end ContinuousRectangleCrossing
end StatMech
