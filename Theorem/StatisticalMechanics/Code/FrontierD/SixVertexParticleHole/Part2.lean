/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexSectorPrefixCount_at_position {N n : ℕ}
    (x : SixVertexSector N n) (i : Fin n) :
    sixVertexSectorPrefixCount x (sixVertexSectorPosition x i) = i.val + 1 := by
  let f := sixVertexSectorPosition x
  have heq : ({j ∈ (x : Finset (Fin N)) | j ≤ f i} : Finset (Fin N)) =
      Finset.image f (Finset.Iic i) := by
    ext j
    constructor
    · intro hj
      simp only [Finset.mem_filter] at hj
      have hjrange : j ∈ Set.range f := by
        rw [show Set.range f = (x.val : Set (Fin N)) by
          change Set.range (x.val.orderEmbOfFin x.prop) = _
          exact Finset.range_orderEmbOfFin x.val x.prop]
        exact hj.1
      obtain ⟨q, rfl⟩ := hjrange
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_Iic.mpr ((f.le_iff_le).mp hj.2), rfl⟩
    · intro hj
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr
        ⟨sixVertexSectorPosition_mem x q,
          (f.le_iff_le).mpr (Finset.mem_Iic.mp hq)⟩
  rw [sixVertexSectorPrefixCount, heq,
    Finset.card_image_of_injective _ f.injective, Fin.card_Iic]

theorem sixVertexSectorPrefixCount_strict_position {N n : ℕ}
    (x : SixVertexSector N n) (i : Fin n) :
    #{j ∈ (x : Finset (Fin N)) | j < sixVertexSectorPosition x i} = i.val := by
  let f := sixVertexSectorPosition x
  have heq : ({j ∈ (x : Finset (Fin N)) | j < f i} : Finset (Fin N)) =
      Finset.image f (Finset.Iio i) := by
    ext j
    constructor
    · intro hj
      simp only [Finset.mem_filter] at hj
      have hjrange : j ∈ Set.range f := by
        rw [show Set.range f = (x.val : Set (Fin N)) by
          change Set.range (x.val.orderEmbOfFin x.prop) = _
          exact Finset.range_orderEmbOfFin x.val x.prop]
        exact hj.1
      obtain ⟨q, rfl⟩ := hjrange
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_Iio.mpr ((f.lt_iff_lt).mp hj.2), rfl⟩
    · intro hj
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr
        ⟨sixVertexSectorPosition_mem x q,
          (f.lt_iff_lt).mpr (Finset.mem_Iio.mp hq)⟩
  rw [heq, Finset.card_image_of_injective _ f.injective, Fin.card_Iio]

theorem sixVertexSectorPosition_le_iff_lt_prefixCount {N n : ℕ}
    (x : SixVertexSector N n) (i : Fin n) (k : Fin N) :
    sixVertexSectorPosition x i ≤ k ↔
      i.val < sixVertexSectorPrefixCount x k := by
  constructor
  · intro hik
    rw [← Nat.add_one_le_iff,
      ← sixVertexSectorPrefixCount_at_position x i]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.trans hik⟩
  · intro hcard
    by_contra! hnot
    have hle : sixVertexSectorPrefixCount x k ≤ i.val := by
      rw [← sixVertexSectorPrefixCount_strict_position x i]
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, hj.2.trans_lt hnot⟩
    omega

theorem sixVertexSectorPrefixCount_le_card {N n : ℕ}
    (x : SixVertexSector N n) (k : Fin N) :
    sixVertexSectorPrefixCount x k ≤ n := by
  calc
    sixVertexSectorPrefixCount x k ≤ (x : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := x.prop


end StatMech.FrontierD
