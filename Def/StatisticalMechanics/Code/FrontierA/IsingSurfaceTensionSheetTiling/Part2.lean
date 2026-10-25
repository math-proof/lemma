/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part2
open Finset
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def tripleTileSheet (n : Nat) (q : Fin 3 × Fin 3) :
    Finset (CubicalPlaquette (tripleTiledSide n) (tripleTiledSide n)
      (tripleTiledSide n)) :=
  let L := tripleTileSide n
  (cubicalXYSheet (a := L) (b := L) (c := L) (0 : Fin (L + 1))).map
    (cubicalPlaquetteChart (A := tripleTiledSide n)
      (B := tripleTiledSide n) (C := tripleTiledSide n)
      (q.1.val * L) (q.2.val * L) (tripleCentralHeight n)
      (tripleTile_fit n q.1) (tripleTile_fit n q.2)
      (tripleTile_height_fit n))

def tripleTileLoop (n : Nat) (q : Fin 3 × Fin 3) :
    Finset (CubicalEdge (tripleTiledSide n) (tripleTiledSide n)
      (tripleTiledSide n)) :=
  let L := tripleTileSide n
  (cubicalXYLoop (a := L) (b := L) (c := L) (0 : Fin (L + 1))).map
    (cubicalEdgeChart (A := tripleTiledSide n)
      (B := tripleTiledSide n) (C := tripleTiledSide n)
      (q.1.val * L) (q.2.val * L) (tripleCentralHeight n)
      (tripleTile_fit n q.1) (tripleTile_fit n q.2)
      (tripleTile_height_fit n))

end
end StatMech.FrontierA
