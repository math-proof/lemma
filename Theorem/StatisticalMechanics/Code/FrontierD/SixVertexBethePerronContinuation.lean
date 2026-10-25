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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorTransferInfinity_apply (N n : Nat)
    (x y : SixVertexSector N n) :
    sixVertexSectorTransferInfinity N n x y =
      if x ≠ y ∧ SixVertexInterlaced (sixVertexSectorRow x)
          (sixVertexSectorRow y) ∧
          sixVertexRowDistance (sixVertexSectorRow x)
            (sixVertexSectorRow y) = 2 * n then 1 else 0 :=
  rfl

theorem sixVertexSectorTransferInfinity_nonneg (N n : Nat)
    (x y : SixVertexSector N n) :
    0 ≤ sixVertexSectorTransferInfinity N n x y := by
  rw [sixVertexSectorTransferInfinity_apply]
  split_ifs <;> norm_num

theorem sixVertexSectorTransferInfinity_symmetric (N n : Nat)
    (x y : SixVertexSector N n) :
    sixVertexSectorTransferInfinity N n x y =
      sixVertexSectorTransferInfinity N n y x := by
  rw [sixVertexSectorTransferInfinity_apply,
    sixVertexSectorTransferInfinity_apply]
  apply if_congr
  · constructor
    · rintro ⟨hxy, hinter, hdist⟩
      exact ⟨Ne.symm hxy, (sixVertexInterlaced_comm _ _).mp hinter,
        (sixVertexRowDistance_comm _ _).symm.trans hdist⟩
    · rintro ⟨hyx, hinter, hdist⟩
      exact ⟨Ne.symm hyx, (sixVertexInterlaced_comm _ _).mp hinter,
        (sixVertexRowDistance_comm _ _).trans hdist⟩
  · rfl
  · rfl


theorem sixVertexSectorRowDistance_le_twice (N n : Nat)
    (x y : SixVertexSector N n) :
    sixVertexRowDistance (sixVertexSectorRow x)
        (sixVertexSectorRow y) ≤ 2 * n := by
  let D : Finset (Fin N) :=
    {i | sixVertexSectorRow x i ≠ sixVertexSectorRow y i}
  have hsub : D ⊆ (x : Finset (Fin N)) ∪ (y : Finset (Fin N)) := by
    intro i hi
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and,
      sixVertexSectorRow_apply] at hi
    simp only [Finset.mem_union]
    by_cases hix : i ∈ (x : Finset (Fin N))
    · exact Or.inl hix
    · right
      by_contra hiy
      simp [hix, hiy] at hi
  calc
    sixVertexRowDistance (sixVertexSectorRow x)
        (sixVertexSectorRow y) = D.card := rfl
    _ ≤ ((x : Finset (Fin N)) ∪ (y : Finset (Fin N))).card :=
      Finset.card_le_card hsub
    _ ≤ (x : Finset (Fin N)).card + (y : Finset (Fin N)).card :=
      Finset.card_union_le _ _
    _ = 2 * n := by rw [x.prop, y.prop]; omega


theorem sixVertexSectorRowDistance_eq_twice_iff_disjoint
    (N n : Nat) (x y : SixVertexSector N n) :
    sixVertexRowDistance (sixVertexSectorRow x)
        (sixVertexSectorRow y) = 2 * n ↔
      Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)) := by
  let D : Finset (Fin N) :=
    {i | sixVertexSectorRow x i ≠ sixVertexSectorRow y i}
  have hD : D = ((x : Finset (Fin N)) \ (y : Finset (Fin N))) ∪
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))) := by
    ext i
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and,
      sixVertexSectorRow_apply, Finset.mem_union, Finset.mem_sdiff]
    by_cases hix : i ∈ (x : Finset (Fin N)) <;>
      by_cases hiy : i ∈ (y : Finset (Fin N)) <;> simp [hix, hiy]
  have hparts : Disjoint
      ((x : Finset (Fin N)) \ (y : Finset (Fin N)))
      ((y : Finset (Fin N)) \ (x : Finset (Fin N))) := by
    rw [Finset.disjoint_left]
    intro i hix hiy
    exact (Finset.mem_sdiff.mp hix).2 (Finset.mem_sdiff.mp hiy).1
  change D.card = 2 * n ↔ _
  rw [hD, Finset.card_union_of_disjoint hparts,
    Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop]
  constructor
  · intro hcard
    have hinterle : ((x : Finset (Fin N)) ∩ (y : Finset (Fin N))).card ≤ n := by
      calc
        ((x : Finset (Fin N)) ∩ (y : Finset (Fin N))).card ≤
            (x : Finset (Fin N)).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = n := x.prop
    rw [Finset.inter_comm (y : Finset (Fin N)) (x : Finset (Fin N))]
      at hcard
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.card_eq_zero.mp
    omega
  · intro hdisj
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    rw [Finset.inter_comm (y : Finset (Fin N)) (x : Finset (Fin N)),
      hdisj]
    simp
    omega


end
end StatMech.FrontierD
