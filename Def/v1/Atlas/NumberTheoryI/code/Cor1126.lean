/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1126.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.NumberTheoryI.code.GlobalFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
import Theorem.v1.Atlas.NumberTheoryI.code.Cor1126.Part2


noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

set_option synthInstance.maxHeartbeats 80000

def completionEmbeddingIntegers {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v) :
    v.adicCompletionIntegers K →ₐ[𝓞 K] w.adicCompletionIntegers L where
  toFun x := ⟨(completionEmbedding_finite v w hw) x.val,
    completionEmbedding_finite_mem_integers v w hw x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  commutes' r := Subtype.ext (completionEmbedding_finite_commutes v w hw r)

def integralTensorToProduct {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    TensorProduct (𝓞 K) (𝓞 L) (v.adicCompletionIntegers K) →ₐ[𝓞 K]
      ((ω : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        ω.val.adicCompletionIntegers L) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom (𝓞 K) _ (fun w =>
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) (w.val.adicCompletionIntegers L))))
    (Pi.algHom (𝓞 K) _ (fun w => completionEmbeddingIntegers v w.val w.prop))

end
