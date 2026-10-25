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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part22
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

def EdgeCopySourceSectorImageEmbedding.toSourceSectorInjection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorImageEmbedding G A B m m') :
    EdgeCopySourceSectorInjection G A B m m' where
  fullSource := I.fullSource
  toFun := fun K _ => K.image I.copyMap
  map_mem := by
    intro K hK
    have hsrc :
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) K = A := by
      simpa [edgeCopySourceSector] using (Finset.mem_filter.mp hK).2
    rw [edgeCopySourceSector, Finset.mem_filter]
    constructor
    · rw [Finset.mem_powerset]
      intro x hx
      simp
    · exact I.sources_image K hsrc
  injective := by
    intro K₁ _hK₁ K₂ _hK₂ hEq
    exact Finset.image_injective I.copyMap_injective hEq


def EdgeCopySourceSectorInsertEmbedding.toSourceSectorInjection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorInsertEmbedding G A B m m') :
    EdgeCopySourceSectorInjection G A B m m' where
  fullSource := I.fullSource
  toFun := fun K _ => insert I.inserted (K.image I.copyMap)
  map_mem := by
    intro K hK
    exact I.insert_mem_edgeCopySourceSector hK
  injective := by
    intro K₁ _hK₁ K₂ _hK₂ hEq
    have hnew₁ : I.inserted ∉ K₁.image I.copyMap := by
      rw [Finset.mem_image]
      rintro ⟨i, _hi, hi⟩
      exact I.inserted_not_mem_image i hi
    have hnew₂ : I.inserted ∉ K₂.image I.copyMap := by
      rw [Finset.mem_image]
      rintro ⟨i, _hi, hi⟩
      exact I.inserted_not_mem_image i hi
    have himage : K₁.image I.copyMap = K₂.image I.copyMap := by
      have herase := congrArg (fun S => S.erase I.inserted) hEq
      simpa [hnew₁, hnew₂] using herase
    exact Finset.image_injective I.copyMap_injective himage


def EdgeCopySourceSectorImageEmbedding.refl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) :
    EdgeCopySourceSectorImageEmbedding G A A m m where
  copyMap := id
  copyMap_injective := Function.injective_id
  fullSource := by
    intro hsrc
    exact hsrc
  sources_image := by
    intro K hsrc
    simpa using hsrc


end Exact3D
end StatMech
