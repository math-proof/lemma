/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part2
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

def oddPrismCriticalSurfaceSpinSquareAverage (n : Nat) : Real :=
  (∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
      oddPrismPlusSpinMean (Ising.betaC 3) n
        (oddPrismLowerHalfSurfaceSite n q.1 q.2).1 ^ 2) /
    (((2 * n + 1 : Nat) : Real) ^ 2)

def criticalCenteredSpinUpGap (r : Nat) : Real :=
  (gvPlusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
      {omega | omega (origin 3) = true} -
    (gvMinusMeasure (boxFinset 3 r) (Ising.betaC 3) 0).real
      {omega | omega (origin 3) = true}

end
end StatMech.FrontierA
