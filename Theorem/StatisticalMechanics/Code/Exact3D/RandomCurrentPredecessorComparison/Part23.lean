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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part21
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem randomCurrent_degK_image_of_vertexEquiv
    {ι κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (ends : ι → Sym2 V) (ends' : κ → Sym2 V)
    (φ : V ≃ V) (copyMap : ι → κ)
    (hcopy : Function.Injective copyMap)
    (hends : ∀ i, ends' (copyMap i) = Sym2.map φ (ends i))
    (K : Finset ι) (x : V) :
    Sharpness.RandomCurrent.degK ends' (K.image copyMap) (φ x) =
      Sharpness.RandomCurrent.degK ends K x := by
  classical
  unfold Sharpness.RandomCurrent.degK
  rw [Finset.filter_image, Finset.card_image_of_injective _ hcopy]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hi, hx⟩
    refine ⟨hi, ?_⟩
    have hx' : φ x ∈ Sym2.map φ (ends i) := by
      simpa [hends i] using hx
    rcases Sym2.mem_map.mp hx' with ⟨y, hy, hφy⟩
    have hyx : y = x := φ.injective hφy
    simpa [hyx] using hy
  · rintro ⟨hi, hx⟩
    refine ⟨hi, ?_⟩
    have hx' : φ x ∈ Sym2.map φ (ends i) :=
      Sym2.mem_map.mpr ⟨x, hx, rfl⟩
    simpa [hends i] using hx'


theorem randomCurrent_sources_image_of_vertexEquiv
    {ι κ V : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V]
    (ends : ι → Sym2 V) (ends' : κ → Sym2 V)
    (φ : V ≃ V) (copyMap : ι → κ)
    (hcopy : Function.Injective copyMap)
    (hends : ∀ i, ends' (copyMap i) = Sym2.map φ (ends i))
    (K : Finset ι) :
    Sharpness.RandomCurrent.sources ends' (K.image copyMap) =
      (Sharpness.RandomCurrent.sources ends K).map φ.toEmbedding := by
  classical
  ext y
  constructor
  · intro hy
    rw [Finset.mem_map]
    refine ⟨φ.symm y, ?_, by simp⟩
    simp only [Sharpness.RandomCurrent.sources, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy ⊢
    have hdeg :=
      randomCurrent_degK_image_of_vertexEquiv
        ends ends' φ copyMap hcopy hends K (φ.symm y)
    have hdeg' :
        Sharpness.RandomCurrent.degK ends' (K.image copyMap) y =
          Sharpness.RandomCurrent.degK ends K (φ.symm y) := by
      simpa using hdeg
    simpa [hdeg'] using hy
  · intro hy
    rw [Finset.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    simp only [Sharpness.RandomCurrent.sources, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx ⊢
    have hdeg :=
      randomCurrent_degK_image_of_vertexEquiv
        ends ends' φ copyMap hcopy hends K x
    simpa [hdeg] using hx


theorem randomCurrent_sources_insert_image_of_vertexEquiv_of_inserted_ends_eq
    {ι κ V : Type*} [DecidableEq κ] [Finite κ] [Fintype V] [DecidableEq V]
    (ends : ι → Sym2 V) (ends' : κ → Sym2 V)
    (φ : V ≃ V) (copyMap : ι → κ)
    (hcopy : Function.Injective copyMap)
    {inserted : κ}
    (hdisjoint : ∀ i, copyMap i ≠ inserted)
    (hends : ∀ i, ends' (copyMap i) = Sym2.map φ (ends i))
    {a b : V}
    (hinserted : ends' inserted = s(a, b))
    (K : Finset ι) :
    Sharpness.RandomCurrent.sources ends' (insert inserted (K.image copyMap)) =
      (Sharpness.RandomCurrent.sources ends K).map φ.toEmbedding ∆
        ({a, b} : Finset V) := by
  classical
  letI := Fintype.ofFinite κ
  have hi :
      inserted ∉ K.image copyMap := by
    rw [Finset.mem_image]
    rintro ⟨i, _hi, hi⟩
    exact hdisjoint i hi
  exact
    randomCurrent_sources_insert_singleton_of_ends_eq
      (ends := ends') (K := K.image copyMap) (i := inserted)
      (A := (Sharpness.RandomCurrent.sources ends K).map φ.toEmbedding)
      (a := a) (b := b) hi
      (randomCurrent_sources_image_of_vertexEquiv
        ends ends' φ copyMap hcopy hends K)
      hinserted


end Exact3D
end StatMech
