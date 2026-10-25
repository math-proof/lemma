/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Structure.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem EdgeCopySourceSectorImageEmbedding.image_mem_edgeCopySourceSector
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorImageEmbedding G A B m m')
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) :
    K.image I.copyMap ∈ edgeCopySourceSector G B m' :=
  (mem_edgeCopySourceSector (G := G) (A := B) (m := m')).mpr
    (I.sources_image K
      ((mem_edgeCopySourceSector (G := G) (A := A) (m := m)).mp hK))


theorem EdgeCopySourceSectorInsertEmbedding.insert_mem_edgeCopySourceSector
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorInsertEmbedding G A B m m')
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) :
    insert I.inserted (K.image I.copyMap) ∈ edgeCopySourceSector G B m' :=
  (mem_edgeCopySourceSector (G := G) (A := B) (m := m')).mpr
    (I.sources_insert K
      ((mem_edgeCopySourceSector (G := G) (A := A) (m := m)).mp hK))

set_option linter.style.longLine false in


theorem EdgeCopySourceSectorInsertEmbedding.insert_mem_edgeCopySourceSectorContainingCopy
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorInsertEmbedding G A B m m')
    {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
    (hK : K ∈ edgeCopySourceSector G A m) :
    insert I.inserted (K.image I.copyMap) ∈
      edgeCopySourceSectorContainingCopy G B m' I.inserted := by
  classical
  exact
    (mem_edgeCopySourceSectorContainingCopy
      (G := G) (A := B) (m := m') (i := I.inserted)
      (K := insert I.inserted (K.image I.copyMap))).mpr
      ⟨I.insert_mem_edgeCopySourceSector hK, by simp⟩

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_le_containingCopy_card_of_insertEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorInsertEmbedding G A B m m') :
    (edgeCopySourceSector G A m).card ≤
      (edgeCopySourceSectorContainingCopy G B m' I.inserted).card := by
  classical
  let φ :
      Finset (Sharpness.FluxEdgeCopy.Copy G m) →
        Finset (Sharpness.FluxEdgeCopy.Copy G m') :=
    fun K =>
      if hK : K ∈ edgeCopySourceSector G A m then
        insert I.inserted (K.image I.copyMap)
      else
        ∅
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · intro K hK
    have hK' : K ∈ edgeCopySourceSector G A m := hK
    simpa [φ, hK'] using
      I.insert_mem_edgeCopySourceSectorContainingCopy hK'
  · intro K₁ hK₁ K₂ hK₂ hEq
    have hK₁' : K₁ ∈ edgeCopySourceSector G A m := hK₁
    have hK₂' : K₂ ∈ edgeCopySourceSector G A m := hK₂
    have hEq' :
        insert I.inserted (K₁.image I.copyMap) =
          insert I.inserted (K₂.image I.copyMap) := by
      simpa [φ, hK₁', hK₂'] using hEq
    have hnew₁ : I.inserted ∉ K₁.image I.copyMap := by
      rw [Finset.mem_image]
      rintro ⟨i, _hi, hi⟩
      exact I.inserted_not_mem_image i hi
    have hnew₂ : I.inserted ∉ K₂.image I.copyMap := by
      rw [Finset.mem_image]
      rintro ⟨i, _hi, hi⟩
      exact I.inserted_not_mem_image i hi
    have himage : K₁.image I.copyMap = K₂.image I.copyMap := by
      have herase := congrArg (fun S => S.erase I.inserted) hEq'
      simpa [hnew₁, hnew₂] using herase
    exact Finset.image_injective I.copyMap_injective himage

set_option linter.style.longLine false in

theorem edgeCopySourceSectorContainingCopy_card_pos_of_sourceSector_card_pos_insertEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorInsertEmbedding G A B m m')
    (hpos : 0 < (edgeCopySourceSector G A m).card) :
    0 < (edgeCopySourceSectorContainingCopy G B m' I.inserted).card :=
  lt_of_lt_of_le hpos
    (edgeCopySourceSector_card_le_containingCopy_card_of_insertEmbedding G I)


end Exact3D
end StatMech
