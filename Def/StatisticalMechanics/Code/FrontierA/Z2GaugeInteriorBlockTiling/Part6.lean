/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInteriorBlockTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSlabGaugeAudit
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInteriorBlockTiling.Part5
open Finset Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def cubicalInteriorBlockBottomSheet (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  cubicalXYSheet (0 : Fin (cubicalInteriorBlockSide L p k + 1))

def cubicalInteriorBlockSlabComplement (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  cubicalLowerComplementSurface (cubicalInteriorBlockHeight L p k)


def cubicalInteriorBlockSideWallFaces (L p k : Nat) :
    Finset (CubicalPlaquette
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)
      (cubicalInteriorBlockSide L p k)) :=
  let N := cubicalInteriorBlockSide L p k
  let castZ : Fin p -> Fin N := Fin.castLE (by
    dsimp [N, cubicalInteriorBlockSide]
    omega)
  ((Finset.univ : Finset (Fin N × Fin p)).image fun iz =>
      CubicalPlaquette.xz iz.1 (0 : Fin (N + 1)) (castZ iz.2)) ∪
  ((Finset.univ : Finset (Fin N × Fin p)).image fun iz =>
      CubicalPlaquette.xz iz.1 (Fin.last N) (castZ iz.2)) ∪
  ((Finset.univ : Finset (Fin N × Fin p)).image fun jz =>
      CubicalPlaquette.yz (0 : Fin (N + 1)) jz.1 (castZ jz.2)) ∪
  ((Finset.univ : Finset (Fin N × Fin p)).image fun jz =>
      CubicalPlaquette.yz (Fin.last N) jz.1 (castZ jz.2))

end
end StatMech.FrontierA
