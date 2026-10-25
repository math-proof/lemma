/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part3
open Finset Matrix


namespace StatMech.FrontierD

@[simp] theorem svRowSectorAt_row {N n : Nat} (x : SixVertexRow N)
    (hx : sixVertexUpCount x = n) :
    sixVertexSectorRow (svRowSectorAt x hx) = x := by
  funext i
  simp [svRowSectorAt, sixVertexSectorRow]

theorem svRowPrefixCount_eq_sector {N n : Nat} (x : SixVertexRow N)
    (hx : sixVertexUpCount x = n) (k : Fin N) :
    svRowPrefixCount x k =
      sixVertexSectorPrefixCount (svRowSectorAt x hx) k := by
  unfold svRowPrefixCount sixVertexSectorPrefixCount
  have hsum :
      (∑ i ∈ Finset.Iic k, (x i).toNat) =
        ((Finset.Iic k).filter fun i => x i = true).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases x i <;> simp
  rw [hsum]
  congr 1
  ext i
  simp [svRowSectorAt, and_comm]

theorem svForwardInterlaced_iff_prefix {N : Nat}
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y) :
    SixVertexForwardInterlaced x y ↔ svRowPrefixForward x y := by
  let xs := svRowSectorAt x rfl
  let ys := svRowSectorAt y hcount.symm
  have hysrow : sixVertexSectorRow ys = y := svRowSectorAt_row y hcount.symm
  have hxsrow : sixVertexSectorRow xs = x := svRowSectorAt_row x rfl
  constructor
  · intro h
    have hpos := sixVertexPositionsForwardInterlaced_of_forward xs ys
      (by simpa [hxsrow, hysrow] using h)
    have hpref := sixVertexSectorPrefixForward_of_positions xs ys hpos
    intro k
    have hk := hpref k
    simpa [svRowPrefixCount_eq_sector, xs, ys, hxsrow, hysrow] using hk
  · intro h
    have hpref : SixVertexSectorPrefixForward xs ys := by
      intro k
      have hk := h k
      simpa [svRowPrefixCount_eq_sector, xs, ys, hxsrow, hysrow] using hk
    have hpos := sixVertexPositionsForwardInterlaced_of_prefix xs ys hpref
    simpa [hxsrow, hysrow] using sixVertexForwardInterlaced_of_positions xs ys hpos

end StatMech.FrontierD
