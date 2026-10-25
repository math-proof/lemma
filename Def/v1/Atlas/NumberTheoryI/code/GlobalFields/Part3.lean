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
import Instance.v1.Atlas.NumberTheoryI.code.GlobalFields.Part2


noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

section TensorProductDecomposition

set_option maxHeartbeats 2000000

set_option synthInstance.maxHeartbeats 80000

def algebraMapLToCompletion {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] (w : NumberField.InfinitePlace L) :
    L →ₐ[K] w.Completion where
  toFun := algebraMap L w.Completion
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun _ => rfl

set_option backward.isDefEq.respectTransparency false in
def completionEmbedding {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K)
    (w : NumberField.InfinitePlace L) (hw : w.comap (algebraMap K L) = v) :
    v.Completion →ₐ[K] w.Completion := by
  haveI : w.1.LiesOver v.1 := ⟨by
    have : (w.comap (algebraMap K L)).1 = v.1 := by rw [hw]
    rw [← this]; rfl⟩
  let iso := LiesOver.isometry_algebraMap w (v := v)
  let f : v.Completion →+* w.Completion := iso.mapRingHom
  exact {
    toRingHom := f
    commutes' := by
      intro r
      show f (algebraMap K v.Completion r) = algebraMap K w.Completion r
      change f (↑(algebraMap K (WithAbs v.1) r)) = ↑(algebraMap K (WithAbs w.1) r)
      rw [iso.mapRingHom_coe]
      congr 1
  }

def canonicalMap {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    TensorProduct K L v.Completion →ₐ[K]
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) :=
  Pi.algHom K
    (fun (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) =>
      w.val.Completion)
    (fun (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) =>
      Algebra.TensorProduct.productMap
        (algebraMapLToCompletion w.val)
        (completionEmbedding v w.val w.prop))

end TensorProductDecomposition
end
