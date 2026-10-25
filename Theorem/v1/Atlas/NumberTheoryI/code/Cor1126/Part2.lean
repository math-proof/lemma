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
import Instance.v1.Atlas.NumberTheoryI.code.Cor1126


noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

set_option synthInstance.maxHeartbeats 80000

theorem completionEmbedding_finite_mem_integers {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v)
    (x : v.adicCompletionIntegers K) :
    (completionEmbedding_finite v w hw) x.val ∈ w.adicCompletionIntegers L := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hx_mem := x.prop
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx_mem


  let emb := completionEmbedding_finite v w hw

  have hclosed : IsClosed {y : v.adicCompletion K |
      Valued.v y ≤ 1 → Valued.v (emb y) ≤ 1} := by


    have h1 : {y : v.adicCompletion K | Valued.v y ≤ 1 → Valued.v (emb y) ≤ 1} =
        {y | ¬(Valued.v y ≤ 1)} ∪ {y | Valued.v (emb y) ≤ 1} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_union]
      tauto
    rw [h1]
    apply IsClosed.union
    ·

      have : {y : v.adicCompletion K | ¬(Valued.v y ≤ 1)} =
          ((Valued.v.valuationSubring : ValuationSubring (v.adicCompletion K)) :
            Set (v.adicCompletion K))ᶜ := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClopen_valuationSubring (v.adicCompletion K)).2.isClosed_compl
    ·
      have hemb_cont : Continuous (emb : v.adicCompletion K → w.adicCompletion L) := by
        show Continuous (UniformSpace.Completion.extensionHom
          (completionEmbedding_finite_ringHom v w)
          (completionEmbedding_finite_continuous v w hw))
        exact UniformSpace.Completion.continuous_extension
      have : {y : v.adicCompletion K | Valued.v (emb y) ≤ 1} =
          (emb : v.adicCompletion K → w.adicCompletion L) ⁻¹'
            ((Valued.v.valuationSubring : ValuationSubring (w.adicCompletion L)) :
              Set (w.adicCompletion L)) := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClosed_valuationSubring (w.adicCompletion L)).preimage hemb_cont

  have hdense : ∀ (k : WithVal (v.valuation K)),
      Valued.v (↑k : v.adicCompletion K) ≤ 1 →
        Valued.v (emb (↑k : v.adicCompletion K)) ≤ 1 := by
    intro k hk
    rw [Valued.valuedCompletion_apply] at hk

    have hemb : (emb (↑k : v.adicCompletion K)) = completionEmbedding_finite_ringHom v w k :=
      UniformSpace.Completion.extensionHom_coe _ (completionEmbedding_finite_continuous v w hw) k
    rw [hemb]


    have hval : Valued.v ((completionEmbedding_finite_ringHom v w) k) =
        w.valuation L (algebraMap K L ((WithVal.equiv (v.valuation K)) k)) := by
      simp only [completionEmbedding_finite_ringHom, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      simp only [Function.comp_apply]
      exact Valued.valuedCompletion_apply _
    rw [hval]
    exact algebraMap_valuation_le_one v w hw _ hk

  exact UniformSpace.Completion.induction_on (x : v.adicCompletion K) hclosed
    (fun k => hdense k) hx_mem

theorem completionEmbedding_finite_commutes {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) (hw : FinitePlace.LiesAbove w v)
    (r : 𝓞 K) :
    (completionEmbedding_finite v w hw)
      ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) r).val) =
    ((algebraMap (𝓞 K) (w.adicCompletionIntegers L) r).val) := by
  have h_lhs : (completionEmbedding_finite v w hw)
      ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) r).val) =
    algebraMap K (w.adicCompletion L) (algebraMap (𝓞 K) K r) := by
    rw [← AlgHom.commutes (completionEmbedding_finite v w hw)]
    congr 1
  rw [h_lhs]
  rw [IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) K L]
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
  rfl

end
