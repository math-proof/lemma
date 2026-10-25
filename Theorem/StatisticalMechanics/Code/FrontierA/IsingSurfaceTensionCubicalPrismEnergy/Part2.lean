/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCubicalPrismEnergy.Part2


namespace StatMech.FrontierA

open scoped BigOperators symmDiff

open Filter Topology

open StatMech StatMech.Ising

noncomputable section

theorem cubicalPlaquetteToOddPrism_leftInverse (n : Nat) :
    Function.LeftInverse (oddPrismToCubicalPlaquette n)
      (cubicalPlaquetteToOddPrism n) := by
  intro p
  cases p with
  | xy x y z =>
      simp only [cubicalPlaquetteToOddPrism]
      split_ifs with hz0 hz1
      · apply congrArg (CubicalPlaquette.xy x y)
        apply Fin.ext
        simp [hz0]
      · apply congrArg (CubicalPlaquette.xy x y)
        apply Fin.ext
        simp [Fin.last, hz1]
      · apply congrArg (CubicalPlaquette.xy x y)
        apply Fin.ext
        simp
        omega
  | xz x y z =>
      simp only [cubicalPlaquetteToOddPrism]
      split_ifs with hy0 hy1
      · apply congrArg (fun y => CubicalPlaquette.xz x y z)
        apply Fin.ext
        simp [hy0]
      · apply congrArg (fun y => CubicalPlaquette.xz x y z)
        apply Fin.ext
        simp [Fin.last, hy1]
      · apply congrArg (fun y => CubicalPlaquette.xz x y z)
        apply Fin.ext
        simp
        omega
  | yz x y z =>
      simp only [cubicalPlaquetteToOddPrism]
      split_ifs with hx0 hx1
      · apply congrArg (fun x => CubicalPlaquette.yz x y z)
        apply Fin.ext
        simp [hx0]
      · apply congrArg (fun x => CubicalPlaquette.yz x y z)
        apply Fin.ext
        simp [Fin.last, hx1]
      · apply congrArg (fun x => CubicalPlaquette.yz x y z)
        apply Fin.ext
        simp
        omega

theorem cubicalPlaquetteToOddPrism_rightInverse (n : Nat) :
    Function.RightInverse (oddPrismToCubicalPlaquette n)
      (cubicalPlaquetteToOddPrism n) := by
  intro q
  cases q <;>
    simp [oddPrismToCubicalPlaquette, cubicalPlaquetteToOddPrism,
      Fin.last] <;>
    omega

end
end StatMech.FrontierA
