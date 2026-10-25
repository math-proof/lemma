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
import Def.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part2
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


theorem gridConnector_mem_support (x y z : Site 2) :
    z ∈ (gridConnector x y).support ↔
      (∃ t : ℤ, t ∈ Set.uIcc (x 0) (y 0) ∧ z = ![t, x 1]) ∨
      (∃ t : ℤ, t ∈ Set.uIcc (x 1) (y 1) ∧ z = ![y 0, t]) := by
  rw [gridConnector, Walk.support_copy, sw_lshape_support_eq]


end ContinuousRectangleCrossing
end StatMech
