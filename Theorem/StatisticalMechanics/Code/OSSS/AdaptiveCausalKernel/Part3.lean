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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part3
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


theorem frozenCodeAtom_eq_rawPairBox (mu : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) :
    frozenCodeAtom mu S base target =
      Set.univ.pi (frozenRawPair mu S base target) := by
  let sigma := realizedEquiv S base
  have hsigma : realizedEquiv S base = sigma := rfl
  ext z
  have hbase :
      codeMap mu (sigma : Fin (Fintype.card E) → E) (fun i => (z i).1) = base ↔
        ∀ i, (z i).1 ∈ StatMech.OSSS.GrandCoupling.rawInterval mu
          (sigma : Fin (Fintype.card E) → E) base i := by
    have h := Set.ext_iff.mp
      (StatMech.OSSS.GrandCoupling.codeMap_fibre_eq_rawbox mu sigma base)
      (fun i => (z i).1)
    simpa [Set.mem_pi] using h
  have htarget :
      codeMap mu (sigma : Fin (Fintype.card E) → E)
          (causalMixLabels S base (fun i => (z i).1) (fun i => (z i).2)) = target ↔
        ∀ i, causalMixLabels S base (fun i => (z i).1) (fun i => (z i).2) i ∈
          StatMech.OSSS.GrandCoupling.rawInterval mu
            (sigma : Fin (Fintype.card E) → E) target i := by
    have h := Set.ext_iff.mp
      (StatMech.OSSS.GrandCoupling.codeMap_fibre_eq_rawbox mu sigma target)
      (causalMixLabels S base (fun i => (z i).1) (fun i => (z i).2))
    simpa [Set.mem_pi] using h
  simp only [frozenCodeAtom, Set.mem_setOf_eq]
  change
    (codeMap mu (sigma : Fin (Fintype.card E) → E) (fun i => (z i).1) = base ∧
      codeMap mu (sigma : Fin (Fintype.card E) → E)
        (causalMixLabels S base (fun i => (z i).1) (fun i => (z i).2)) = target) ↔
      z ∈ Set.univ.pi (frozenRawPair mu S base target)
  rw [hbase, htarget]
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨hb, ht⟩ i
    specialize hb i
    specialize ht i
    simp only [frozenRawPair, hsigma]
    by_cases hi : independentAt S base (sigma i)
    · simpa [hi, causalMixLabels, hsigma] using And.intro hb ht
    · simpa [hi, causalMixLabels, hsigma] using And.intro hb ht
  · intro h
    constructor
    · intro i
      specialize h i
      simp only [frozenRawPair, hsigma] at h
      by_cases hi : independentAt S base (sigma i)
      · simp only [hi, if_true, Set.mem_prod] at h
        exact h.1
      · simp only [hi, Bool.false_eq_true, if_false, Set.mem_prod, Set.mem_inter_iff,
          Set.mem_univ, and_true] at h
        exact h.1
    · intro i
      specialize h i
      simp only [frozenRawPair, hsigma] at h
      by_cases hi : independentAt S base (sigma i)
      · simp only [hi, if_true, Set.mem_prod] at h
        simpa [causalMixLabels, hsigma, hi] using h.2
      · simp only [hi, Bool.false_eq_true, if_false, Set.mem_prod, Set.mem_inter_iff,
          Set.mem_univ, and_true] at h
        simpa [causalMixLabels, hsigma, hi] using h.2


end AdaptiveCausalKernel
end OSSS
end StatMech
