/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part11
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexSectorPosition_rotatedTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : q 0 < 0) :
    sixVertexSectorPosition
      (sixVertexBetheRotatedTupleSector x q hq hfree hq0) =
      sixVertexBetheRotatedTupleEmbedding x q hq hfree hq0 := by
  change Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv
      (sixVertexBetheRotatedTupleEmbedding x q hq hfree hq0)) = _
  exact Equiv.symm_apply_apply _ _

theorem sixVertexSectorIntCoordinates_rotatedTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : q 0 < 0) :
    sixVertexSectorIntCoordinates
      (sixVertexBetheRotatedTupleSector x q hq hfree hq0) =
      sixVertexBetheUnshiftCoordinates N q := by
  funext i
  unfold sixVertexSectorIntCoordinates
  rw [sixVertexSectorPosition_rotatedTupleSector]
  unfold sixVertexBetheRotatedTupleEmbedding
  simp only [OrderEmbedding.coe_ofStrictMono]
  change ((sixVertexBetheUnshiftCoordinates N q i).toNat : Int) = _
  exact Int.toNat_of_nonneg
    (sixVertexBetheUnshiftCoordinates_nonnegative x q hq i)

theorem sixVertexBetheRotatedTupleSector_forward
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : q 0 < 0) :
    SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow (sixVertexBetheRotatedTupleSector x q hq hfree hq0)) := by
  apply sixVertexForwardInterlaced_of_positions
  constructor
  · intro i
    have hcoord := sixVertexSectorIntCoordinates_rotatedTupleSector
      x q hq hfree hq0
    induction i using Fin.lastCases with
    | last =>
        have hqzero := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq 0
        have hle : sixVertexSectorIntCoordinates x (Fin.last n) ≤ q 0 + N := by
          have := hqzero.1
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero] at this
          omega
        have hlast := congrFun hcoord (Fin.last n)
        simp only [sixVertexBetheUnshiftCoordinates, Fin.lastCases_last] at hlast
        have hle' : sixVertexSectorIntCoordinates x (Fin.last n) ≤
            sixVertexSectorIntCoordinates
              (sixVertexBetheRotatedTupleSector x q hq hfree hq0)
                (Fin.last n) := hle.trans hlast.ge
        unfold sixVertexSectorIntCoordinates at hle'
        exact_mod_cast hle'
    | cast i =>
        have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
        have hshift : sixVertexBetheShiftCoordinates N
            (sixVertexSectorIntCoordinates x) i.succ =
            sixVertexSectorIntCoordinates x i.castSucc := by
          simp [sixVertexBetheShiftCoordinates]
        have hri := congrFun hcoord i.castSucc
        simp only [sixVertexBetheUnshiftCoordinates,
          Fin.lastCases_castSucc] at hri
        have hle : sixVertexSectorIntCoordinates x i.castSucc ≤
            sixVertexSectorIntCoordinates
              (sixVertexBetheRotatedTupleSector x q hq hfree hq0)
                i.castSucc := (hshift ▸ hi.1).trans hri.ge
        unfold sixVertexSectorIntCoordinates at hle
        exact_mod_cast hle
  · intro k hk
    let i : Fin n := ⟨k, by omega⟩
    have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
    have hcoord := congrFun
      (sixVertexSectorIntCoordinates_rotatedTupleSector x q hq hfree hq0)
      i.castSucc
    simp only [sixVertexBetheUnshiftCoordinates,
      Fin.lastCases_castSucc] at hcoord
    have hle : sixVertexSectorIntCoordinates
        (sixVertexBetheRotatedTupleSector x q hq hfree hq0) i.castSucc ≤
        sixVertexSectorIntCoordinates x i.succ := hcoord.le.trans hi.2
    unfold sixVertexSectorIntCoordinates at hle
    exact_mod_cast hle

theorem sixVertexReverseTuple_mem
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) ∈
      sixVertexBetheCyclicIntervalTuples N
        (sixVertexSectorIntCoordinates x) := by
  rw [mem_sixVertexBetheCyclicIntervalTuples]
  have hpos := (sixVertexForwardInterlaced_iff_positions x y).mp hxy
  intro i
  induction i using Fin.cases with
  | zero =>
      simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero]
      constructor
      · have hle : sixVertexSectorIntCoordinates x (Fin.last n) ≤
            sixVertexSectorIntCoordinates y (Fin.last n) := by
          unfold sixVertexSectorIntCoordinates
          exact_mod_cast hpos.1 (Fin.last n)
        exact sub_le_sub_right hle (N : Int)
      · have hylt : sixVertexSectorIntCoordinates y (Fin.last n) < N := by
          unfold sixVertexSectorIntCoordinates
          exact_mod_cast (sixVertexSectorPosition y (Fin.last n)).prop
        have hxzero : 0 ≤ sixVertexSectorIntCoordinates x 0 := by
          simp [sixVertexSectorIntCoordinates]
        omega
  | succ i =>
      simp only [sixVertexBetheShiftCoordinates, Fin.cases_succ]
      constructor
      · unfold sixVertexSectorIntCoordinates
        exact_mod_cast hpos.1 i.castSucc
      · unfold sixVertexSectorIntCoordinates
        exact_mod_cast hpos.2 i.val (by omega)

theorem sixVertexReverseTuple_first_neg
    {N n : Nat} (y : SixVertexSector N (n + 1)) :
    sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y) 0 < 0 := by
  simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero]
  unfold sixVertexSectorIntCoordinates
  have := (sixVertexSectorPosition y (Fin.last n)).prop
  omega

theorem sixVertexReverseTuple_collisionFree
    {N n : Nat} (x y : SixVertexSector N (n + 1)) :
    sixVertexBetheCollisionSet N (sixVertexSectorIntCoordinates x)
      (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y)) = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨i, hi⟩
  have hcol := (mem_sixVertexBetheCollisionSet N _ _ i).mp hi
  induction i using Fin.cases with
  | zero =>
      have hneg := sixVertexReverseTuple_first_neg y
      have hxzero : 0 ≤ sixVertexSectorIntCoordinates x 0 := by
        simp [sixVertexSectorIntCoordinates]
      exact (not_lt_of_ge hxzero) (hcol.1 ▸ hneg)
  | succ i =>
      have hfirst : sixVertexSectorIntCoordinates y i.castSucc =
          sixVertexSectorIntCoordinates x i.succ := by
        simpa [sixVertexBetheShiftCoordinates] using hcol.1
      by_cases hwrap : finRotate (n + 1) i.succ = 0
      · have hilast : i.succ = Fin.last n := by
          apply (finRotate (n + 1)).injective
          simpa using hwrap
        have hsecond : sixVertexSectorIntCoordinates y (Fin.last n) =
            sixVertexSectorIntCoordinates x (Fin.last n) := by
          have h := hcol.2
          rw [hwrap] at h
          simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero] at h
          have h' : sixVertexSectorIntCoordinates y (Fin.last n) - N =
              sixVertexSectorIntCoordinates x (Fin.last n) - N := by
            simpa [hilast] using h
          omega
        have hilt : i.castSucc < Fin.last n := by
          exact_mod_cast i.prop
        have hystrict := (sixVertexSectorPosition y).strictMono hilt
        have heq : sixVertexSectorIntCoordinates y i.castSucc =
            sixVertexSectorIntCoordinates y (Fin.last n) := by
          calc
            _ = sixVertexSectorIntCoordinates x i.succ := hfirst
            _ = sixVertexSectorIntCoordinates x (Fin.last n) := by rw [hilast]
            _ = sixVertexSectorIntCoordinates y (Fin.last n) := hsecond.symm
        have hystrictInt : sixVertexSectorIntCoordinates y i.castSucc <
            sixVertexSectorIntCoordinates y (Fin.last n) := by
          unfold sixVertexSectorIntCoordinates
          exact_mod_cast hystrict
        exact hystrictInt.ne heq
      · obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hwrap
        have hjval : j.castSucc = i.succ := by
          apply Fin.ext
          have hval : (finRotate (n + 1) i.succ).val = j.val + 1 := by
            simpa using congrArg Fin.val hj
          have hilast : i.succ ≠ Fin.last n := by
            intro hilast
            apply hwrap
            rw [hilast]
            apply Fin.ext
            simp
          have hrotval : (finRotate (n + 1) i.succ).val = i.succ.val + 1 :=
            coe_finRotate_of_ne_last hilast
          exact Nat.add_right_cancel (hval.symm.trans hrotval)
        have hsecond : sixVertexSectorIntCoordinates y j.castSucc =
            sixVertexSectorIntCoordinates x i.succ := by
          have h := hcol.2
          rw [hj] at h
          simpa [sixVertexBetheShiftCoordinates, hjval] using h
        have hystrict := (sixVertexSectorPosition y).strictMono
          (show i.castSucc < j.castSucc by
            rw [hjval]
            exact Fin.castSucc_lt_succ)
        have heq : sixVertexSectorIntCoordinates y i.castSucc =
            sixVertexSectorIntCoordinates y j.castSucc :=
          hfirst.trans hsecond.symm
        have hystrictInt : sixVertexSectorIntCoordinates y i.castSucc <
            sixVertexSectorIntCoordinates y j.castSucc := by
          unfold sixVertexSectorIntCoordinates
          exact_mod_cast hystrict
        exact hystrictInt.ne heq

theorem sixVertexRotatedTupleSector_reverseTuple
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hxy : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    sixVertexBetheRotatedTupleSector x
      (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))
      (sixVertexReverseTuple_mem x y hxy)
      (sixVertexReverseTuple_collisionFree x y)
      (sixVertexReverseTuple_first_neg y) = y := by
  apply (Set.powersetCard.ofFinEmbEquiv
    (n := n + 1) (I := Fin N)).symm.injective
  change sixVertexSectorPosition _ = sixVertexSectorPosition y
  ext i
  have hcoord := congrFun (sixVertexSectorIntCoordinates_rotatedTupleSector
    x (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))
      (sixVertexReverseTuple_mem x y hxy)
      (sixVertexReverseTuple_collisionFree x y)
      (sixVertexReverseTuple_first_neg y)) i
  have hcoord' : sixVertexSectorIntCoordinates
      (sixVertexBetheRotatedTupleSector x
        (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y))
        (sixVertexReverseTuple_mem x y hxy)
        (sixVertexReverseTuple_collisionFree x y)
        (sixVertexReverseTuple_first_neg y)) i =
      sixVertexSectorIntCoordinates y i := by
    calc
      _ = sixVertexBetheUnshiftCoordinates N
          (sixVertexBetheShiftCoordinates N (sixVertexSectorIntCoordinates y)) i :=
        hcoord
      _ = _ := congrFun (sixVertexBetheUnshiftCoordinates_shift N
        (sixVertexSectorIntCoordinates y)) i
  unfold sixVertexSectorIntCoordinates at hcoord'
  exact_mod_cast hcoord'


end
end StatMech.FrontierD
