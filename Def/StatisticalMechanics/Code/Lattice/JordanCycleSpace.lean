/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part2
open SimpleGraph Set List Function


namespace StatMech

namespace Lattice

def jcs_JordanRegion (S : Set (Site 2)) : Prop :=
  (∃ x, x ∈ S) ∧ (∃ y, y ∉ S) ∧
    (∀ a b : Site 2, a ∈ S → b ∈ S → (latticeMinusBarrier S).Reachable a b) ∧
    (∀ a b : Site 2, a ∉ S → b ∉ S → (latticeMinusBarrier S).Reachable a b)


end Lattice
end StatMech
