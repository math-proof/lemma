/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part8
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexBetheDirectTupleEmbedding
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : 0 ≤ q 0) :
    Fin (n + 1) ↪o Fin N := by
  have hnonneg := sixVertexBetheTuple_nonnegative x q hq hq0
  let f : Fin (n + 1) -> Fin N := fun i =>
    ⟨(q i).toNat, by
      rw [Int.toNat_lt (hnonneg i)]
      have hi := (mem_sixVertexBetheCyclicIntervalTuples N _ q).mp hq i
      have hxlt : sixVertexSectorIntCoordinates x i < (N : Int) := by
        unfold sixVertexSectorIntCoordinates
        exact_mod_cast (sixVertexSectorPosition x i).prop
      exact hi.2.trans_lt hxlt⟩
  refine OrderEmbedding.ofStrictMono f ?_
  intro i j hij
  have hqij := sixVertexBetheCollisionFreeTuple_strictMono x q hq hfree hij
  change (q i).toNat < (q j).toNat
  rw [← Int.ofNat_lt]
  simpa [Int.toNat_of_nonneg (hnonneg i), Int.toNat_of_nonneg (hnonneg j)]
    using hqij


noncomputable def sixVertexBetheDirectTupleSector
    {N n : Nat} (x : SixVertexSector N (n + 1))
    (q : Fin (n + 1) -> Int)
    (hq : q ∈ sixVertexBetheCyclicIntervalTuples N
      (sixVertexSectorIntCoordinates x))
    (hfree : sixVertexBetheCollisionSet N
      (sixVertexSectorIntCoordinates x) q = ∅) (hq0 : 0 ≤ q 0) :
    SixVertexSector N (n + 1) :=
  Set.powersetCard.ofFinEmbEquiv
    (sixVertexBetheDirectTupleEmbedding x q hq hfree hq0)

end
end StatMech.FrontierD
