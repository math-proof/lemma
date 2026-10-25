/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalReduction
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityVaryingTemperature.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingMinusTIFromPlacement
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part2
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Lattice StatMech.ConfigSpace StatMech.FK
  StatMech.Sharpness

noncomputable section

variable {d : Nat}


def oddPrismLowerHalfCenter (n : Nat) :
    {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n // v.z.val <= n} :=
  ⟨⟨⟨n, by omega⟩, ⟨n, by omega⟩, ⟨n, by omega⟩⟩, le_rfl⟩


def oddPrismLowerHalfSurfaceSite (n : Nat)
    (i j : Fin (2 * n + 1)) :
    {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n // v.z.val <= n} :=
  ⟨⟨i, j, ⟨n, by omega⟩⟩, le_rfl⟩


def oddPrismLowerHalfSurfaceSpinMean (beta : Real) (n : Nat) : Real :=
  let K := oddPrismInternalGraph n
  let P : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Prop :=
    fun v => v.z.val <= n
  expJ (K.comap (Subtype.val : {v // P v} -> _)).edgeFinset
    (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
    (fun sigma => spin sigma (oddPrismLowerHalfCenter n))

def oddPrismLowerHalfSurfaceSpinMeanAt (beta : Real) (n : Nat)
    (i j : Fin (2 * n + 1)) : Real :=
  let K := oddPrismInternalGraph n
  let P : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Prop :=
    fun v => v.z.val <= n
  expJ (K.comap (Subtype.val : {v // P v} -> _)).edgeFinset
    (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
    (fun sigma => spin sigma (oddPrismLowerHalfSurfaceSite n i j))


end
end StatMech.FrontierA
