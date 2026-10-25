/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Theorem.v1.Atlas.NumberTheoryI.code.GlobalFields


noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

section TensorProductDecomposition

set_option maxHeartbeats 2000000

set_option synthInstance.maxHeartbeats 80000

def completionEmbedding_finite {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    v.adicCompletion K →ₐ[K] w.adicCompletion L :=
  AlgHom.mk'
    (UniformSpace.Completion.extensionHom
      (completionEmbedding_finite_ringHom v w)
      (completionEmbedding_finite_continuous v w hw))
    (fun k x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      show (UniformSpace.Completion.extensionHom
        (completionEmbedding_finite_ringHom v w)
        (completionEmbedding_finite_continuous v w hw))
        (algebraMap K (v.adicCompletion K) k) =
        algebraMap K (w.adicCompletion L) k
      have : algebraMap K (v.adicCompletion K) k =
        (↑(algebraMap K (WithVal (v.valuation K)) k) : v.adicCompletion K) := rfl
      rw [this, UniformSpace.Completion.extensionHom_coe]
      rfl)

def algebraMapLToAdicCompletion {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    L →ₐ[K] w.adicCompletion L where
  toFun := algebraMap L (w.adicCompletion L)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun _ => rfl

def canonicalMap_finite {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    TensorProduct K L (v.adicCompletion K) →ₐ[K]
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L) :=
  Pi.algHom K
    (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      w.val.adicCompletion L)
    (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      Algebra.TensorProduct.productMap
        (algebraMapLToAdicCompletion w.val)
        (completionEmbedding_finite v w.val w.prop))

set_option synthInstance.maxHeartbeats 80000 in

def corollary_13_7_orbit_equiv
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K] :
    Quotient (MulAction.orbitRel (K ≃ₐ[k] K) (NumberField.InfinitePlace K)) ≃
      NumberField.InfinitePlace k :=
  InfinitePlace.orbitRelEquiv

def ComplexEmbedding.conjugateSetoid (L : Type*) [Field L] :
    Setoid (L →+* ℂ) where
  r φ ψ := InfinitePlace.mk φ = InfinitePlace.mk ψ
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def corollary_13_7_embedding_orbit_equiv_Q (L : Type*) [Field L] :
    Quotient (ComplexEmbedding.conjugateSetoid L) ≃
      NumberField.InfinitePlace L where
  toFun := Quotient.lift InfinitePlace.mk (fun _ _ h => h)
  invFun w := Quotient.mk (ComplexEmbedding.conjugateSetoid L) w.embedding
  left_inv := by
    intro q
    exact Quotient.inductionOn q fun φ => by
      simp only [Quotient.lift_mk]
      exact Quotient.sound (mk_embedding (mk φ))
  right_inv := by
    intro w
    simp only [Quotient.lift_mk]
    exact w.mk_embedding

def EmbeddingsAbove (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) : Type _ :=
  { φ : L →+* ℂ // (InfinitePlace.mk φ).comap (algebraMap K L) = v }

def conjugateSetoidAbove {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Setoid (EmbeddingsAbove K v (L := L)) where
  r φ ψ := InfinitePlace.mk φ.val = InfinitePlace.mk ψ.val
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

def corollary_13_7_embeddings_equiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    Quotient (conjugateSetoidAbove v (K := K) (L := L)) ≃
      { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v } where
  toFun := Quotient.lift
    (fun (φ : EmbeddingsAbove K v) =>
      (⟨InfinitePlace.mk φ.val, by rw [comap_mk]; exact φ.prop⟩ :
        { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }))
    (fun φ ψ (h : InfinitePlace.mk φ.val = InfinitePlace.mk ψ.val) => by
      simp only [Subtype.mk.injEq]
      exact h)
  invFun w := by
    refine Quotient.mk (conjugateSetoidAbove v) ⟨w.val.embedding, ?_⟩
    rw [comap_mk]
    rw [← comap_mk]
    rw [w.val.mk_embedding]
    exact w.prop
  left_inv := by
    intro q
    exact Quotient.inductionOn q fun ⟨φ, hφ⟩ => by
      simp only [Quotient.lift_mk]
      apply Quotient.sound
      show InfinitePlace.mk (InfinitePlace.mk φ).embedding = InfinitePlace.mk φ
      exact (InfinitePlace.mk φ).mk_embedding
  right_inv := by
    intro ⟨w, hw⟩
    simp only [Quotient.lift_mk, Subtype.mk.injEq]
    exact w.mk_embedding

end TensorProductDecomposition
end
