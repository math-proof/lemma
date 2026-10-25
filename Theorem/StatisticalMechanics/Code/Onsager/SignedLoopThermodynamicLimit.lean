/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierA
  StatMech.FrontierB

noncomputable section

theorem ons_int_bounds_of_natAbs_le {n : Nat} {z : Int}
    (hz : z.natAbs <= n) : -(n : Int) <= z ∧ z <= n := by
  rcases Int.natAbs_eq z with hz' | hz' <;> omega


end
end StatMech.Onsager
