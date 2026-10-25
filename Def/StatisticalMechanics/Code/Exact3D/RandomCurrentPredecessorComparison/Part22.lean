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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part23
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

def EdgeCopySourceSectorImageEmbedding.ofVertexEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (φ : V ≃ V)
    (copyEquiv :
      Sharpness.FluxEdgeCopy.Copy G m ≃
        Sharpness.FluxEdgeCopy.Copy G m')
    (hends :
      ∀ i,
        Sharpness.FluxEdgeCopy.endsM G m' (copyEquiv i) =
          Sym2.map φ (Sharpness.FluxEdgeCopy.endsM G m i))
    (hAB : A.map φ.toEmbedding = B) :
    EdgeCopySourceSectorImageEmbedding G A B m m' where
  copyMap := copyEquiv
  copyMap_injective := copyEquiv.injective
  fullSource := by
    intro hsrc
    have huniv :
        (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m)).image copyEquiv =
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy G m')) := by
      ext i
      simp
    have hmap :=
      randomCurrent_sources_image_of_vertexEquiv
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Sharpness.FluxEdgeCopy.endsM G m')
        φ copyEquiv copyEquiv.injective hends
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m))
    rw [huniv] at hmap
    simpa [hsrc, hAB] using hmap
  sources_image := by
    intro K hsrc
    have hmap :=
      randomCurrent_sources_image_of_vertexEquiv
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Sharpness.FluxEdgeCopy.endsM G m')
        φ copyEquiv copyEquiv.injective hends K
    simpa [hsrc, hAB] using hmap


def EdgeCopySourceSectorInsertEmbedding.ofVertexEquivAndInsertedPair
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (φ : V ≃ V)
    (copyMap :
      Sharpness.FluxEdgeCopy.Copy G m →
        Sharpness.FluxEdgeCopy.Copy G m')
    (hcopy : Function.Injective copyMap)
    (inserted : Sharpness.FluxEdgeCopy.Copy G m')
    (hdisjoint : ∀ i, copyMap i ≠ inserted)
    (hends :
      ∀ i,
        Sharpness.FluxEdgeCopy.endsM G m' (copyMap i) =
          Sym2.map φ (Sharpness.FluxEdgeCopy.endsM G m i))
    {a b : V}
    (hinserted :
      Sharpness.FluxEdgeCopy.endsM G m' inserted = s(a, b))
    (hAB : A.map φ.toEmbedding ∆ ({a, b} : Finset V) = B)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A →
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m')
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) = B) :
    EdgeCopySourceSectorInsertEmbedding G A B m m' where
  copyMap := copyMap
  copyMap_injective := hcopy
  inserted := inserted
  inserted_not_mem_image := hdisjoint
  fullSource := hfull
  sources_insert := by
    intro K hsrc
    have hsrc_insert :=
      randomCurrent_sources_insert_image_of_vertexEquiv_of_inserted_ends_eq
        (ends := Sharpness.FluxEdgeCopy.endsM G m)
        (ends' := Sharpness.FluxEdgeCopy.endsM G m')
        φ copyMap hcopy hdisjoint hends hinserted K
    simpa [hsrc, hAB] using hsrc_insert


def EdgeCopySourceSectorInsertEmbedding.ofVertexEquivAndInsertedPair_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (φ : V ≃ V)
    (copyMap :
      Sharpness.FluxEdgeCopy.Copy G m →
        Sharpness.FluxEdgeCopy.Copy G m')
    (hcopy : Function.Injective copyMap)
    (inserted : Sharpness.FluxEdgeCopy.Copy G m')
    (hdisjoint : ∀ i, copyMap i ≠ inserted)
    (hends :
      ∀ i,
        Sharpness.FluxEdgeCopy.endsM G m' (copyMap i) =
          Sym2.map φ (Sharpness.FluxEdgeCopy.endsM G m i))
    {a b : V}
    (hinserted :
      Sharpness.FluxEdgeCopy.endsM G m' inserted = s(a, b))
    (hAB : A.map φ.toEmbedding ∆ ({a, b} : Finset V) = B)
    (huniv :
      insert inserted
          ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)).image
            copyMap) =
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m'))) :
    EdgeCopySourceSectorInsertEmbedding G A B m m' :=
  EdgeCopySourceSectorInsertEmbedding.ofVertexEquivAndInsertedPair
    (G := G) (A := A) (B := B) (m := m) (m' := m')
    φ copyMap hcopy inserted hdisjoint hends hinserted hAB
    (by
      intro hsrc
      have hsrc_insert :=
        randomCurrent_sources_insert_image_of_vertexEquiv_of_inserted_ends_eq
          (ends := Sharpness.FluxEdgeCopy.endsM G m)
          (ends' := Sharpness.FluxEdgeCopy.endsM G m')
          φ copyMap hcopy hdisjoint hends hinserted
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m))
      rw [huniv] at hsrc_insert
      simpa [hsrc, hAB] using hsrc_insert)


def EdgeCopySourceSectorInsertEmbedding.ofEndpointPreservingInsertedPair
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (copyMap :
      Sharpness.FluxEdgeCopy.Copy G m →
        Sharpness.FluxEdgeCopy.Copy G m')
    (hcopy : Function.Injective copyMap)
    (inserted : Sharpness.FluxEdgeCopy.Copy G m')
    (hdisjoint : ∀ i, copyMap i ≠ inserted)
    (hends :
      ∀ i,
        Sharpness.FluxEdgeCopy.endsM G m' (copyMap i) =
          Sharpness.FluxEdgeCopy.endsM G m i)
    {a b : V}
    (hinserted :
      Sharpness.FluxEdgeCopy.endsM G m' inserted = s(a, b))
    (hAB : A ∆ ({a, b} : Finset V) = B)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A →
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m')
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) = B) :
    EdgeCopySourceSectorInsertEmbedding G A B m m' :=
  EdgeCopySourceSectorInsertEmbedding.ofVertexEquivAndInsertedPair
    (G := G) (A := A) (B := B) (m := m) (m' := m')
    (Equiv.refl V) copyMap hcopy inserted hdisjoint
    (by
      intro i
      simpa using hends i)
    hinserted
    (by simpa using hAB)
    hfull


def EdgeCopySourceSectorInsertEmbedding.ofEndpointPreservingInsertedPair_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (copyMap :
      Sharpness.FluxEdgeCopy.Copy G m →
        Sharpness.FluxEdgeCopy.Copy G m')
    (hcopy : Function.Injective copyMap)
    (inserted : Sharpness.FluxEdgeCopy.Copy G m')
    (hdisjoint : ∀ i, copyMap i ≠ inserted)
    (hends :
      ∀ i,
        Sharpness.FluxEdgeCopy.endsM G m' (copyMap i) =
          Sharpness.FluxEdgeCopy.endsM G m i)
    {a b : V}
    (hinserted :
      Sharpness.FluxEdgeCopy.endsM G m' inserted = s(a, b))
    (hAB : A ∆ ({a, b} : Finset V) = B)
    (huniv :
      insert inserted
          ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)).image
            copyMap) =
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m'))) :
    EdgeCopySourceSectorInsertEmbedding G A B m m' :=
  EdgeCopySourceSectorInsertEmbedding.ofVertexEquivAndInsertedPair_univ
    (G := G) (A := A) (B := B) (m := m) (m' := m')
    (Equiv.refl V) copyMap hcopy inserted hdisjoint
    (by
      intro i
      simpa using hends i)
    hinserted
    (by simpa using hAB)
    huniv


noncomputable def edgeCopyIncrementMap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    Sharpness.FluxEdgeCopy.Copy G m →
      Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)) := by
  intro i
  rcases i with ⟨e, k⟩
  by_cases he : e = e0
  · subst e
    exact ⟨e0, ⟨k.val, by rw [Function.update_self]; omega⟩⟩
  · have hupdate : Function.update m e0 (m e0 + 1) e = m e := by
      rw [Function.update_of_ne he]
    exact ⟨e, Fin.cast hupdate.symm k⟩


noncomputable def edgeCopyIncrementInserted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    Sharpness.FluxEdgeCopy.Copy G (Function.update m e0 (m e0 + 1)) :=
  ⟨e0, ⟨m e0, by rw [Function.update_self]; omega⟩⟩


end Exact3D
end StatMech
