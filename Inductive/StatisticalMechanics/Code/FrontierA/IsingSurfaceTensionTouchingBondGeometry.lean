/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.Ising StatMech.IsingFK
  StatMech.Percolation


inductive OddPrismTouchIndex (n : Nat)
  | xInternal (x : Fin (2 * n)) (y z : Fin (2 * n + 1))
  | yInternal (x : Fin (2 * n + 1)) (y : Fin (2 * n))
      (z : Fin (2 * n + 1))
  | zInternal (x y : Fin (2 * n + 1)) (z : Fin (2 * n))
  | xZero (y z : Fin (2 * n + 1))
  | xLast (y z : Fin (2 * n + 1))
  | yZero (x z : Fin (2 * n + 1))
  | yLast (x z : Fin (2 * n + 1))
  | zZero (x y : Fin (2 * n + 1))
  | zLast (x y : Fin (2 * n + 1))
  deriving DecidableEq, Fintype

end StatMech.FrontierA
