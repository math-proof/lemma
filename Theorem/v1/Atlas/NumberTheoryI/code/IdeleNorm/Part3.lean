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
import Def.v1.Atlas.NumberTheoryI.code.IdeleNorm.Part3


noncomputable section

open NumberField IsDedekindDomain Ideles

theorem finiteNormComponent_mem_integers_almost_all (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (b : FiniteAdeleRing (𝓞 L) L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (finiteNormComponent K L v) b ∈ v.adicCompletionIntegers K := by

  have hb := b.2
  rw [Filter.Eventually, Filter.mem_cofinite] at hb ⊢

  have hgood : ∀ v : HeightOneSpectrum (𝓞 K),
      (∀ w ∈ HeightOneSpectrum.placesAbove v (L := L),
        b w ∈ w.adicCompletionIntegers L) →
      finiteNormComponent K L v b ∈ v.adicCompletionIntegers K := by
    intro v hv_int
    simp only [finiteNormComponent, MonoidHom.coe_mk, OneHom.coe_mk]
    apply (v.adicCompletionIntegers K).prod_mem
    intro ⟨w, hw_mem⟩ _
    exact HeightOneSpectrum.localNormHom_mem_integers w v
      (HeightOneSpectrum.liesOver_of_mem_placesAbove hw_mem) (b w) (hv_int w hw_mem)


  let underMap : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 K) := fun w =>
    ⟨w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)),
     Ideal.comap_isPrime _ w.asIdeal,
     Ideal.IsIntegralClosure.comap_ne_bot L w.ne_bot⟩

  apply Set.Finite.subset (hb.image underMap)
  intro v hv
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hv

  have : ¬ ∀ w ∈ HeightOneSpectrum.placesAbove v (L := L),
      (b : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) w ∈
        w.adicCompletionIntegers L := by
    intro h_all
    exact hv (hgood v h_all)
  push Not at this
  obtain ⟨w, hw_mem, hw_bad⟩ := this
  refine ⟨w, ?_, ?_⟩
  ·
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    exact hw_bad
  ·
    have hmem := (HeightOneSpectrum.finite_placesAbove v).mem_toFinset.mp hw_mem
    simp only [Set.mem_setOf_eq] at hmem
    exact HeightOneSpectrum.ext hmem

end
