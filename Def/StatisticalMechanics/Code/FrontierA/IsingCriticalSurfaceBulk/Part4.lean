/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part4
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

def oddPrismCriticalLowerHalfSpinSquareAverage (n : Nat) : Real :=
  (∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
      oddPrismLowerHalfSurfaceSpinMeanAt (Ising.betaC 3) n q.1 q.2 ^ 2) /
    (((2 * n + 1 : Nat) : Real) ^ 2)

end
end StatMech.FrontierA
