/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part4
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def centralLowerBottomVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun xy => some (CubicalCell.mk xy.1 xy.2 (centralBottomZ n)))

def centralLowerWestVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun yz => some (CubicalCell.mk 0 yz.1 (centralLowerZ yz.2)))

def centralLowerEastVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun yz => some
      (CubicalCell.mk (Fin.last n) yz.1 (centralLowerZ yz.2)))

def centralLowerSouthVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun xz => some (CubicalCell.mk xz.1 0 (centralLowerZ xz.2)))

def centralLowerNorthVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  (Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
    (fun xz => some
      (CubicalCell.mk xz.1 (Fin.last n) (centralLowerZ xz.2)))


def centralLowerBoundaryVertices (n : Nat) : Finset
    (CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :=
  centralLowerBottomVertices n ∪ centralLowerWestVertices n ∪
    centralLowerEastVertices n ∪ centralLowerSouthVertices n ∪
      centralLowerNorthVertices n

end
end StatMech.FrontierA
