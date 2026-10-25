/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part6
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexSectorPosition_alternatingEven
    (N n : Nat) (hhalf : 2 * n ≤ N) :
    sixVertexSectorPosition (sixVertexAlternatingEvenSector N n hhalf) =
      sixVertexAlternatingEvenEmbedding hhalf := by
  change Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv (sixVertexAlternatingEvenEmbedding hhalf)) = _
  exact Equiv.symm_apply_apply _ _

@[simp] theorem sixVertexSectorPosition_alternatingOdd
    (N n : Nat) (hhalf : 2 * n ≤ N) :
    sixVertexSectorPosition (sixVertexAlternatingOddSector N n hhalf) =
      sixVertexAlternatingOddEmbedding hhalf := by
  change Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv (sixVertexAlternatingOddEmbedding hhalf)) = _
  exact Equiv.symm_apply_apply _ _

@[simp] theorem sixVertexSectorPosition_alternatingEven_apply_val
    (N n : Nat) (hhalf : 2 * n ≤ N) (k : Fin n) :
    (sixVertexSectorPosition
      (sixVertexAlternatingEvenSector N n hhalf) k).val = 2 * k.val := by
  rw [sixVertexSectorPosition_alternatingEven]
  rfl

@[simp] theorem sixVertexSectorPosition_alternatingOdd_apply_val
    (N n : Nat) (hhalf : 2 * n ≤ N) (k : Fin n) :
    (sixVertexSectorPosition
      (sixVertexAlternatingOddSector N n hhalf) k).val = 2 * k.val + 1 := by
  rw [sixVertexSectorPosition_alternatingOdd]
  rfl

theorem sixVertexAlternatingEvenSector_noAdjacent
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    SixVertexSectorNoAdjacent
      (sixVertexAlternatingEvenSector N n hhalf) := by
  constructor
  · intro k hk
    simp only [sixVertexSectorPosition_alternatingEven,
      sixVertexAlternatingEvenEmbedding, OrderEmbedding.coe_ofStrictMono,
      Fin.val_mk]
    omega
  · intro hn'
    simp only [sixVertexSectorPosition_alternatingEven,
      sixVertexAlternatingEvenEmbedding, OrderEmbedding.coe_ofStrictMono,
      Fin.val_mk]
    omega

theorem sixVertexAlternatingOddSector_noAdjacent
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    SixVertexSectorNoAdjacent
      (sixVertexAlternatingOddSector N n hhalf) := by
  constructor
  · intro k hk
    simp only [sixVertexSectorPosition_alternatingOdd,
      sixVertexAlternatingOddEmbedding, OrderEmbedding.coe_ofStrictMono,
      Fin.val_mk]
    omega
  · intro hn'
    simp only [sixVertexSectorPosition_alternatingOdd,
      sixVertexAlternatingOddEmbedding, OrderEmbedding.coe_ofStrictMono,
      Fin.val_mk]
    omega

theorem sixVertexAlternatingEven_disjoint_odd
    {N n : Nat} (hhalf : 2 * n ≤ N) :
    Disjoint
      ((sixVertexAlternatingEvenSector N n hhalf : SixVertexSector N n) :
        Finset (Fin N))
      ((sixVertexAlternatingOddSector N n hhalf : SixVertexSector N n) :
        Finset (Fin N)) := by
  rw [Finset.disjoint_left]
  intro z hzEven hzOdd
  have hzEven' : z ∈ Set.range (sixVertexAlternatingEvenEmbedding hhalf) := by
    exact (Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range
      (sixVertexAlternatingEvenEmbedding hhalf) z).mp hzEven
  have hzOdd' : z ∈ Set.range (sixVertexAlternatingOddEmbedding hhalf) := by
    exact (Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range
      (sixVertexAlternatingOddEmbedding hhalf) z).mp hzOdd
  obtain ⟨i, hi⟩ := hzEven'
  obtain ⟨j, hj⟩ := hzOdd'
  have hval := congrArg Fin.val (hi.trans hj.symm)
  simp only [sixVertexAlternatingEvenEmbedding,
    sixVertexAlternatingOddEmbedding, OrderEmbedding.coe_ofStrictMono,
    Fin.val_mk] at hval
  omega


theorem sixVertexInfinityGraph_adj_alternating
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    (sixVertexInfinityGraph N n).Adj
      (sixVertexAlternatingEvenSector N n hhalf)
      (sixVertexAlternatingOddSector N n hhalf) := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hpos := congrArg
      (fun x : SixVertexSector N n => (sixVertexSectorPosition x ⟨0, hn⟩).val)
      heq
    simp only [sixVertexSectorPosition_alternatingEven,
      sixVertexSectorPosition_alternatingOdd,
      sixVertexAlternatingEvenEmbedding, sixVertexAlternatingOddEmbedding,
      OrderEmbedding.coe_ofStrictMono, Fin.val_mk] at hpos
    omega
  · left
    apply sixVertexForwardInterlaced_of_positions
    constructor
    · intro i
      rw [sixVertexSectorPosition_alternatingEven,
        sixVertexSectorPosition_alternatingOdd]
      change (2 * i.val : Nat) ≤ 2 * i.val + 1
      omega
    · intro k hk
      rw [sixVertexSectorPosition_alternatingEven,
        sixVertexSectorPosition_alternatingOdd]
      change (2 * k + 1 : Nat) ≤ 2 * (k + 1)
      omega
  · exact (sixVertexSectorRowDistance_eq_twice_iff_disjoint N n _ _).mpr
      (sixVertexAlternatingEven_disjoint_odd hhalf)

end
end StatMech.FrontierD
