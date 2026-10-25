/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part9
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexSectorPosition_directTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : 0 ≤ q 0) :
    sixVertexSectorPosition
      (sixVertexBetheDirectTupleSector x q hq hfree hq0) =
      sixVertexBetheDirectTupleEmbedding x q hq hfree hq0 := by
  change Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv
      (sixVertexBetheDirectTupleEmbedding x q hq hfree hq0)) = _
  exact Equiv.symm_apply_apply _ _

theorem sixVertexSectorIntCoordinates_directTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : 0 ≤ q 0) :
    sixVertexSectorIntCoordinates
      (sixVertexBetheDirectTupleSector x q hq hfree hq0) = q := by
  funext i
  unfold sixVertexSectorIntCoordinates
  rw [sixVertexSectorPosition_directTupleSector]
  change ((q i).toNat : Int) = q i
  exact Int.toNat_of_nonneg
    (sixVertexBetheTuple_nonnegative x q hq hq0 i)

theorem sixVertexBetheDirectTupleSector_forward
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : 0 ≤ q 0) :
    SixVertexForwardInterlaced
      (sixVertexSectorRow (sixVertexBetheDirectTupleSector x q hq hfree hq0))
      (sixVertexSectorRow x) := by
  apply sixVertexForwardInterlaced_of_positions
  constructor
  · intro i
    have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i
    have hcoord := congrFun
      (sixVertexSectorIntCoordinates_directTupleSector x q hq hfree hq0) i
    have hle : ((sixVertexSectorPosition
        (sixVertexBetheDirectTupleSector x q hq hfree hq0) i).val : Int) ≤
        (sixVertexSectorPosition x i).val := by
      simpa [sixVertexSectorIntCoordinates] using hcoord.le.trans hi.2
    exact_mod_cast hle
  · intro k hk
    let i : Fin n := ⟨k, by omega⟩
    have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
    have hshift : sixVertexBetheShiftCoordinates N
        (sixVertexSectorIntCoordinates x) i.succ =
        sixVertexSectorIntCoordinates x i.castSucc := by
      simp [sixVertexBetheShiftCoordinates]
    have hcoord := congrFun
      (sixVertexSectorIntCoordinates_directTupleSector x q hq hfree hq0) i.succ
    have hcoord' : ((sixVertexSectorPosition
        (sixVertexBetheDirectTupleSector x q hq hfree hq0) i.succ).val : Int) =
        q i.succ := by
      simpa only [sixVertexSectorIntCoordinates] using hcoord
    have hle : ((sixVertexSectorPosition x i.castSucc).val : Int) ≤
        (sixVertexSectorPosition
          (sixVertexBetheDirectTupleSector x q hq hfree hq0) i.succ).val := by
      have hbase : sixVertexSectorIntCoordinates x i.castSucc ≤ q i.succ :=
        hshift ▸ hi.1
      simpa only [sixVertexSectorIntCoordinates] using hbase.trans hcoord'.ge
    exact_mod_cast hle

theorem sixVertexForwardTuple_mem
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    sixVertexSectorIntCoordinates y ∈
      sixVertexBetheCyclicIntervalTuples N
        (sixVertexSectorIntCoordinates x) := by
  rw [mem_sixVertexBetheCyclicIntervalTuples]
  have hpos := (sixVertexForwardInterlaced_iff_positions y x).mp hyx
  intro i
  constructor
  · induction i using Fin.cases with
    | zero =>
        simp only [sixVertexBetheShiftCoordinates, sixVertexSectorIntCoordinates,
          Fin.cases_zero]
        have hxlast := (sixVertexSectorPosition x (Fin.last n)).prop
        have hyzero : 0 ≤ (sixVertexSectorPosition y 0).val := Nat.zero_le _
        omega
    | succ i =>
        simp only [sixVertexBetheShiftCoordinates, sixVertexSectorIntCoordinates,
          Fin.cases_succ]
        exact_mod_cast hpos.2 i.val (by omega)
  · unfold sixVertexSectorIntCoordinates
    exact_mod_cast hpos.1 i

theorem sixVertexForwardTuple_collisionFree
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    sixVertexBetheCollisionSet N (sixVertexSectorIntCoordinates x)
      (sixVertexSectorIntCoordinates y) = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨i, hi⟩
  have hcol := (mem_sixVertexBetheCollisionSet N _ _ i).mp hi
  induction i using Fin.lastCases with
  | last =>
      have hrot : finRotate (n + 1) (Fin.last n) = 0 := by
        apply Fin.ext
        simp
      have hyzero : 0 ≤ sixVertexSectorIntCoordinates y 0 := by
        simp [sixVertexSectorIntCoordinates]
      have hxlast : sixVertexSectorIntCoordinates x (Fin.last n) < N := by
        unfold sixVertexSectorIntCoordinates
        exact_mod_cast (sixVertexSectorPosition x (Fin.last n)).prop
      have hthis := hcol.2
      rw [hrot] at hthis
      simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero] at hthis
      omega
  | cast i =>
      have hnext : finRotate (n + 1) i.castSucc = i.succ := by
        apply Fin.ext
        simp
      have hystrict := (sixVertexSectorPosition y).strictMono
        (Fin.castSucc_lt_succ (i := i))
      have heq : sixVertexSectorIntCoordinates y i.castSucc =
          sixVertexSectorIntCoordinates y i.succ := by
        calc
          _ = sixVertexSectorIntCoordinates x i.castSucc := hcol.1
          _ = sixVertexBetheShiftCoordinates N
              (sixVertexSectorIntCoordinates x) i.succ := by
                simp [sixVertexBetheShiftCoordinates]
          _ = sixVertexSectorIntCoordinates y i.succ := by
                simpa [hnext] using hcol.2.symm
      have hystrictInt : sixVertexSectorIntCoordinates y i.castSucc <
          sixVertexSectorIntCoordinates y i.succ := by
        unfold sixVertexSectorIntCoordinates
        exact_mod_cast hystrict
      exact hystrictInt.ne heq

theorem sixVertexDirectTupleSector_forwardTuple
    {N n : Nat} (x y : SixVertexSector N (n + 1))
    (hyx : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x)) :
    sixVertexBetheDirectTupleSector x (sixVertexSectorIntCoordinates y)
      (sixVertexForwardTuple_mem x y hyx)
      (sixVertexForwardTuple_collisionFree x y hyx)
      (by simp [sixVertexSectorIntCoordinates]) = y := by
  apply (Set.powersetCard.ofFinEmbEquiv
    (n := n + 1) (I := Fin N)).symm.injective
  change sixVertexSectorPosition _ = sixVertexSectorPosition y
  rw [sixVertexSectorPosition_directTupleSector]
  ext i
  change (sixVertexSectorIntCoordinates y i).toNat =
    (sixVertexSectorPosition y i).val
  simp [sixVertexSectorIntCoordinates]


end
end StatMech.FrontierD
