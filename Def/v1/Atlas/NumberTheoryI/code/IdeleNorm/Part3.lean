/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdeleNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.Ideles.Part3
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ideles
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Theorem.v1.Atlas.NumberTheoryI.code.IdeleNorm.Part2


noncomputable section

open NumberField IsDedekindDomain Ideles

def finiteNormComponent (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    FiniteAdeleRing (𝓞 L) L →* v.adicCompletion K where
  toFun b := (HeightOneSpectrum.placesAbove v (L := L)).attach.prod fun w =>
    HeightOneSpectrum.localNormHom w.1 v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove w.2) (b w.1)
  map_one' := by
    apply Finset.prod_eq_one
    intro w _
    exact (HeightOneSpectrum.localNormHom w.1 v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove w.2)).map_one
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    congr 1
    ext w
    exact (HeightOneSpectrum.localNormHom w.1 v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove w.2)).map_mul _ _

end
