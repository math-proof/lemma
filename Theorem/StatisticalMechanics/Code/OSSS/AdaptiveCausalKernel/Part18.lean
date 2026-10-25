/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part18
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace OSSS

namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma measurable_tripleCausalOutputs (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    Measurable (tripleCausalOutputs μ S base) := by
  let σ := realizedEquiv S.leftOrder base
  have hU : Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
      fun i => (z i).1.1) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))
  have hV : Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
      fun i => (z i).1.2) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))
  have hV' : Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
      fun i => (z i).2) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_snd.comp (measurable_pi_apply i)
  have hmix (C : CausalOrder (Finset.univ : Finset E))
      (hW : Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
        fun i => if independentAt C base (realizedEquiv C base i)
          then (z i).1.2 else (z i).1.1)) :
      Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
        codeMap μ (σ : Fin (Fintype.card E) → E)
          (causalMixLabels C base (fun i => (z i).1.1) (fun i => (z i).1.2))) := by
    exact (GrandCoupling.measurable_codeMap μ σ).comp (by simpa [causalMixLabels] using hW)
  have hmix' (C : CausalOrder (Finset.univ : Finset E))
      (hW : Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
        fun i => if independentAt C base (realizedEquiv C base i)
          then (z i).2 else (z i).1.1)) :
      Measurable (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) =>
        codeMap μ (σ : Fin (Fintype.card E) → E)
          (causalMixLabels C base (fun i => (z i).1.1) (fun i => (z i).2))) := by
    exact (GrandCoupling.measurable_codeMap μ σ).comp (by simpa [causalMixLabels] using hW)
  have hleftLabels : Measurable
      (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) => fun i =>
        if independentAt S.leftOrder base (realizedEquiv S.leftOrder base i)
          then (z i).1.2 else (z i).1.1) := by
    apply measurable_pi_lambda
    intro i
    split
    · exact measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))
    · exact measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))
  have hrightLabels : Measurable
      (fun z : Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ) => fun i =>
        if independentAt S.rightOrder base (realizedEquiv S.rightOrder base i)
          then (z i).2 else (z i).1.1) := by
    apply measurable_pi_lambda
    intro i
    split
    · exact measurable_snd.comp (measurable_pi_apply i)
    · exact measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))
  exact ((GrandCoupling.measurable_codeMap μ σ).comp hU).prodMk
    ((hmix S.leftOrder hleftLabels).prodMk (hmix' S.rightOrder hrightLabels))

theorem tripleCausalOutputs_fibre (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    {z | tripleCausalOutputs μ S base z = (base, left, right)} =
      frozenCrossCodeAtom μ S base left right := by
  ext z
  simp only [tripleCausalOutputs, frozenCrossCodeAtom, Set.mem_setOf_eq, Prod.mk.injEq]

end AdaptiveCausalKernel
end OSSS
end StatMech
