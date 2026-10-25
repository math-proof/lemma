/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFreeLeftContinuous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.CorrelationMonotone
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Ising Lattice Percolation Sharpness

variable {d : Nat}

noncomputable def currentContinuityFreeBoxTwoPoint
    (d n : Nat) (beta : Real) (x y : Site d) : Real :=
  ∫ omega, spinProd ({x, y} : Finset (Site d)) omega
    ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))

end StatMech.FrontierB
