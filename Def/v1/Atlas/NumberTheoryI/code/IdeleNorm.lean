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


noncomputable section

open NumberField IsDedekindDomain Ideles

def InfinitePlace.localNormHom {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : InfinitePlace L) (v : InfinitePlace K) :
    w.Completion →* v.Completion := by
  classical
  exact
    if hv : v.IsReal then
      if hw : w.IsReal then

        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom.comp
          (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMonoidHom
      else

        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom.comp
          (Complex.normSq.toMonoidHom.comp
            (InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (InfinitePlace.not_isReal_iff_isComplex.mp hw)).toMonoidHom)
    else
      if hw : w.IsReal then

        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).symm.toMonoidHom.comp
          (Complex.ofRealHom.toMonoidHom.comp
            (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMonoidHom)
      else

        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).symm.toMonoidHom.comp
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).toMonoidHom

open Classical in
def infiniteNormComponent (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : InfinitePlace K) :
    InfiniteAdeleRing L →* v.Completion where
  toFun b := ∏ w : InfinitePlace L,
    if w.comap (algebraMap K L) = v then
      InfinitePlace.localNormHom w v (b w)
    else 1
  map_one' := by
    apply Finset.prod_eq_one
    intro w _
    split_ifs with h
    · exact (InfinitePlace.localNormHom w v).map_one
    · rfl
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    congr 1
    ext w
    split_ifs with h
    · exact (InfinitePlace.localNormHom w v).map_mul _ _
    · exact (mul_one 1).symm

def infiniteAdeleNormHom (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    InfiniteAdeleRing L →* InfiniteAdeleRing K :=
  Pi.monoidHom (fun v => infiniteNormComponent K L v)

def HeightOneSpectrum.adicCompletionAlgebra {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K))
    (hw : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal) :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  instAlgebraAdicCompletionOfLiesOver K v w hw

def HeightOneSpectrum.localNormHom {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K))
    (hw : v.asIdeal ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal) :
    (w.adicCompletion L →* v.adicCompletion K) :=
  letI := HeightOneSpectrum.adicCompletionAlgebra w v hw
  Algebra.norm (v.adicCompletion K)

end
