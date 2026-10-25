/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalPaddedWilsonExpectation_mono
    {beta : Real} (hbeta : 0 ≤ beta) (a b : Nat)
    {lx rx ly ry lz rz LX RX LY RY LZ RZ : Nat}
    (hlx : lx ≤ LX) (hrx : rx ≤ RX)
    (hly : ly ≤ LY) (hry : ry ≤ RY)
    (hlz : lz ≤ LZ) (hrz : rz ≤ RZ) :
    cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz ≤
      cubicalPaddedWilsonExpectation beta a b LX RX LY RY LZ RZ := by
  let oldX := lx + a + rx
  let oldY := ly + b + ry
  let oldZ := lz + rz
  let newX := LX + a + RX
  let newY := LY + b + RY
  let newZ := LZ + RZ
  let outer := cubicalEdgeChart (LX - lx) (LY - ly) (LZ - lz)
    (a := oldX) (b := oldY) (c := oldZ)
    (A := newX) (B := newY) (C := newZ)
    (by dsimp [oldX, newX]; omega)
    (by dsimp [oldY, newY]; omega)
    (by dsimp [oldZ, newZ]; omega)
  let inner := cubicalEdgeChart lx ly lz
    (a := a) (b := b) (c := 0)
    (A := oldX) (B := oldY) (C := oldZ)
    (by dsimp [oldX]; omega) (by dsimp [oldY]; omega)
    (by dsimp [oldZ]; omega)
  let target := cubicalEdgeChart LX LY LZ
    (a := a) (b := b) (c := 0)
    (A := newX) (B := newY) (C := newZ)
    (by dsimp [newX]; omega) (by dsimp [newY]; omega)
    (by dsimp [newZ]; omega)
  let L := cubicalXYLoop (a := a) (b := b) (c := 0) (0 : Fin 1)
  have hmap : (L.map inner).map outer = L.map target := by
    rw [Finset.map_map]
    congr 1
    ext e
    change outer (inner e) = target e
    simpa [outer, inner, target, oldX, oldY, oldZ, newX, newY, newZ,
      Nat.sub_add_cancel hlx, Nat.sub_add_cancel hly,
      Nat.sub_add_cancel hlz, add_assoc] using
      (cubicalEdgeChart_comp_apply lx ly lz (LX - lx) (LY - ly) (LZ - lz)
        (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) e)
  have h := cubicalWilsonExpectation_le_chart
    (a := oldX) (b := oldY) (c := oldZ)
    (A := newX) (B := newY) (C := newZ)
    (LX - lx) (LY - ly) (LZ - lz)
    (by dsimp [oldX, newX]; omega)
    (by dsimp [oldY, newY]; omega)
    (by dsimp [oldZ, newZ]; omega) hbeta (L.map inner)
  rw [hmap] at h
  simpa [cubicalPaddedWilsonExpectation, oldX, oldY, oldZ,
    newX, newY, newZ, inner, target, L] using h


end
end StatMech.FrontierA
