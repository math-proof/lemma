/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingBlockSource.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part2


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


theorem fkRectWindingBlockPathVertex_first
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) :
    fkRectWindingBlockPathVertex k scale blocks cut x hx 0 =
      fkRectRightBandRowOne
        (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change 1 = 1
    rfl

theorem fkRectWindingBlockPathVertex_last
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) :
    fkRectWindingBlockPathVertex k scale blocks cut x hx
        (Fin.last (blocks + 1)) =
      fkRectRightBandLastRow
        (fkRectWindingBlockVerticalFamily k scale blocks) cut x hx := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change 1 + 2 * (scale + 1) * (blocks + 1) =
      (fkRectWindingBlockVerticalFamily k scale blocks).height - 1
    simp only [fkRectWindingBlockVerticalFamily_height]
    omega


theorem fkRectWindingBlockPathPairs_card_le
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) :
    (connectionPathPairs (blocks + 1)
      (fkRectWindingBlockPathVertex k scale blocks cut x hx)).card <=
        blocks + 1 :=
  connectionPathPairs_card_le _ _

theorem fkRectWindingBlockPath_pairMap_injective
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) :
    Function.Injective (fun i : Fin (blocks + 1) =>
      (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc,
        fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ)) := by
  intro i j hij
  have hrow := congrArg (fun pair => pair.1.1.2.val) hij
  change 1 + 2 * (scale + 1) * i.val =
    1 + 2 * (scale + 1) * j.val at hrow
  have hmul : 2 * (scale + 1) * i.val =
      2 * (scale + 1) * j.val := Nat.add_left_cancel hrow
  apply Fin.ext
  exact Nat.mul_left_cancel (by positivity) hmul

theorem fkRectWindingBlockPathPairs_card_eq
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) :
    (connectionPathPairs (blocks + 1)
      (fkRectWindingBlockPathVertex k scale blocks cut x hx)).card =
        blocks + 1 := by
  rw [connectionPathPairs, Finset.card_image_of_injective _
    (fkRectWindingBlockPath_pairMap_injective k scale blocks cut x hx)]
  simp

theorem mem_fkRectWindingBlockPathPairs_iff
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val)
    (xy : FKRectRightStripBandVertex
        (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
        ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1) ×
      FKRectRightStripBandVertex
        (fkRectWindingBlockVerticalFamily k scale blocks) cut 1
        ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1)) :
    xy ∈ connectionPathPairs (blocks + 1)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx) ↔
      ∃ i : Fin (blocks + 1),
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc,
          fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ) = xy := by
  rw [connectionPathPairs, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hxy⟩
    exact ⟨i, hxy⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, Finset.mem_univ _, rfl⟩


theorem fkRectWindingBlockPathVertex_squarePoint_step
    (k scale blocks cut : Nat)
    (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width)
    (hx : cut <= x.val) (i : Fin (blocks + 1)) :
    fkRectVertexSquarePoint (fkRectWindingBlockVerticalFamily k scale blocks)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ).1 -
      fkRectVertexSquarePoint (fkRectWindingBlockVerticalFamily k scale blocks)
        (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc).1 =
      (((scale + 1 : Nat) : Int), -((scale + 1 : Nat) : Int)) := by
  apply Prod.ext
  · simp [fkRectVertexSquarePoint, fkRectWindingBlockPathVertex,
      fkRectSquareDevelopPoint]
    rw [show (1 : Int) + 2 * (scale + 1) * (i.val + 1) + 1 =
          2 * ((scale + 1) * (i.val + 1) + 1) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num),
      show (1 : Int) + 2 * (scale + 1) * i.val + 1 =
          2 * ((scale + 1) * i.val + 1) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
    ring
  · simp [fkRectVertexSquarePoint, fkRectWindingBlockPathVertex,
      fkRectSquareDevelopPoint]
    have hodd (z : Int) : (1 + 2 * z) / 2 = z := by omega
    have hcur :
        ((1 : Int) + 2 * (scale + 1) * i.val) / 2 =
          (scale + 1) * i.val := by
      convert hodd ((scale + 1) * i.val) using 1 <;> ring
    have hnext :
        ((1 : Int) + 2 * (scale + 1) * (i.val + 1)) / 2 =
          (scale + 1) * (i.val + 1) := by
      convert hodd ((scale + 1) * (i.val + 1)) using 1 <;> ring
    rw [hcur, hnext]
    ring


end
end StatMech.FrontierD
