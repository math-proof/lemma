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
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part4
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


def InUnitSquare (p : Fin 2 → ℝ) : Prop :=
  ∀ i, 0 ≤ p i ∧ p i ≤ 1

end ContinuousRectangleCrossing
end StatMech
