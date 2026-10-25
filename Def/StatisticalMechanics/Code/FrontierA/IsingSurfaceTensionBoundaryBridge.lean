/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoundaryBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularModel.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing.Part4
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
open Filter Topology
open scoped symmDiff


namespace StatMech.FrontierA

noncomputable section

def rectangularPrismInterfaceDensity (beta : Real) (n : Nat) : Real :=
  StatMech.Ising.rectangularDobrushinFreeEnergy
      1 beta (2 * n + 1) (2 * n + 1) n /
    ((2 * n + 1 : Nat) : Real) ^ 2


def oddCubicalIsingDisorderDensity (beta : Real) (n : Nat) : Real :=
  rectangularSurfaceDensity (rectangularIsingDobrushinFreeEnergy beta)
    (2 * n + 1) (2 * n + 1)


def standardCubicInterfaceDensity (beta : Real) (n : Nat) : Real :=
  StatMech.Ising.finiteInterfaceFreeEnergy
      (d := 3) (⟨2, by omega⟩ : Fin 3) n beta /
    ((2 * n + 1 : Nat) : Real) ^ 2


def centralCubicalIsingDisorderDensity (beta : Real) (n : Nat) : Real :=
  let L := 2 * n + 1
  multibondDisorderFreeEnergy
      (cubicalDualEnds (a := L) (b := L) (c := L))
      (fun _ : CubicalPlaquette L L L => beta)
      (cubicalXYSheet (a := L) (b := L) (c := L)
        (⟨n + 1, by omega⟩ : Fin (L + 1))) /
    ((L : Nat) : Real) ^ 2


end
end StatMech.FrontierA
