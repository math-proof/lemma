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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part6
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


lemma measurable_pairedCausalOutputs (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    Measurable (pairedCausalOutputs mu S base) := by
  let σ := realizedEquiv S.leftOrder base
  let split : (Fin (Fintype.card E) → (ℝ × ℝ)) →
      (Fin (Fintype.card E) → ℝ) × (Fin (Fintype.card E) → ℝ) :=
    fun z => (fun i => (z i).1, fun i => (z i).2)
  have hsplit : Measurable split := by
    have hU : Measurable (fun z : Fin (Fintype.card E) → (ℝ × ℝ) =>
        fun i => (z i).1) := by
      apply measurable_pi_lambda
      intro i
      exact measurable_fst.comp (measurable_pi_apply i)
    have hV : Measurable (fun z : Fin (Fintype.card E) → (ℝ × ℝ) =>
        fun i => (z i).2) := by
      apply measurable_pi_lambda
      intro i
      exact measurable_snd.comp (measurable_pi_apply i)
    exact hU.prodMk hV
  have hbase : Measurable (fun p : (Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ) =>
        codeMap mu (σ : Fin (Fintype.card E) → E) p.1) :=
    (GrandCoupling.measurable_codeMap mu σ).comp measurable_fst
  have hleft : Measurable (fun p : (Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ) =>
        codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S.leftOrder base p.1 p.2)) :=
    (GrandCoupling.measurable_codeMap mu σ).comp
      (measurable_causalMixLabels_prod S.leftOrder base)
  have hright : Measurable (fun p : (Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ) =>
        codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S.rightOrder base p.1 p.2)) :=
    (GrandCoupling.measurable_codeMap mu σ).comp
      (measurable_causalMixLabels_prod S.rightOrder base)
  change Measurable ((fun p => (codeMap mu (σ : Fin (Fintype.card E) → E) p.1,
    codeMap mu (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.leftOrder base p.1 p.2),
    codeMap mu (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.rightOrder base p.1 p.2))) ∘ split)
  exact (hbase.prodMk (hleft.prodMk hright)).comp hsplit

theorem pairedCausalOutputs_fibre (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    {z | pairedCausalOutputs mu S base z = (base, left, right)} =
      frozenTripleCodeAtom mu S base left right := by
  ext z
  simp only [pairedCausalOutputs, frozenTripleCodeAtom, frozenCodeAtom,
    Set.mem_setOf_eq, Set.mem_inter_iff, Prod.mk.injEq]
  rw [realizedEquiv_leftOrder_eq_rightOrder S base]
  tauto

end AdaptiveCausalKernel
end OSSS
end StatMech
