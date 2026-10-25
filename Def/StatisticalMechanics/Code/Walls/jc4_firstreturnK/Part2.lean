/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


noncomputable def jc4_firstReturnK (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i) : ℕ :=
  open Classical in Nat.find hex


end Walls
end StatMech
