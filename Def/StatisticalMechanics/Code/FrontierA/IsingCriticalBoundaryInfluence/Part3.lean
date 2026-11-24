module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalReduction
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part7
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityVaryingTemperature.Part2
public import Theorem.StatisticalMechanics.Code.Ising.IsingMinusTIFromPlacement
public import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
public import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part3
open Filter MeasureTheory Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Lattice StatMech.ConfigSpace StatMech.FK
  StatMech.Sharpness

noncomputable section

variable {d : Nat}


noncomputable def criticalCenteredSlab (L H : Nat) : Finset (Site 3) :=
  (boxFinset 3 (max L H)).filter fun x =>
    (x 0).natAbs ≤ L ∧ (x 1).natAbs ≤ L ∧ (x 2).natAbs ≤ H

end
end StatMech.FrontierA
