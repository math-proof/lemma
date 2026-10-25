/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part10
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexBetheRotatedTupleEmbedding
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : q 0 < 0) :
    Fin (n + 1) ↪o Fin N := by
  have hnonneg := sixVertexBetheUnshiftCoordinates_nonnegative x q hq
  let r := sixVertexBetheUnshiftCoordinates N q
  let f : Fin (n + 1) -> Fin N := fun i =>
    ⟨(r i).toNat, by
      rw [Int.toNat_lt (hnonneg i)]
      induction i using Fin.lastCases with
      | last =>
          simp only [r, sixVertexBetheUnshiftCoordinates, Fin.lastCases_last]
          omega
      | cast i =>
          have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i.succ
          have hxlt : sixVertexSectorIntCoordinates x i.succ < (N : Int) := by
            unfold sixVertexSectorIntCoordinates
            exact_mod_cast (sixVertexSectorPosition x i.succ).prop
          simp only [r, sixVertexBetheUnshiftCoordinates,
            Fin.lastCases_castSucc]
          exact hi.2.trans_lt hxlt⟩
  refine OrderEmbedding.ofStrictMono f ?_
  intro i j hij
  have hrij := sixVertexBetheUnshiftCoordinates_strictMono x q hq hfree hij
  change (r i).toNat < (r j).toNat
  have hrjpos : 0 < r j := (hnonneg i).trans_lt hrij
  exact (Int.toNat_lt_toNat hrjpos).mpr hrij

noncomputable def sixVertexBetheRotatedTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : q 0 < 0) :
    SixVertexSector N (n + 1) :=
  Set.powersetCard.ofFinEmbEquiv
    (sixVertexBetheRotatedTupleEmbedding x q hq hfree hq0)

end
end StatMech.FrontierD
