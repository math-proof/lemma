/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempVertexField.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonPlusLimit.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
open Finset SimpleGraph MeasureTheory
open scoped BigOperators Classical


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


noncomputable def plusBoundaryEdges (Lambda : Finset (Site d)) :
    Finset (Sym2 (Site d)) :=
  (gvBondTouch Lambda).filter (fun e ↦ ¬ edgeInside Lambda e)


noncomputable def plusBoundaryField (Lambda : Finset (Site d))
    (x : {v // v ∈ Lambda}) : ℝ :=
  ((plusBoundaryEdges Lambda).filter (fun e ↦ x.1 ∈ e)).card

end Sharpness
end StatMech
