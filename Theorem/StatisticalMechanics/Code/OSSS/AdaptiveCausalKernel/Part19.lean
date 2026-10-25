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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part19
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


theorem frozenCrossCodeAtom_eq_rawTripleBox (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    frozenCrossCodeAtom μ S base left right =
      Set.univ.pi (crossRawTriple μ S base left right) := by
  let σ := realizedEquiv S.leftOrder base
  have hσ : realizedEquiv S.leftOrder base = σ := rfl
  have hσr : realizedEquiv S.rightOrder base = σ := by
    rw [← hσ, realizedEquiv_leftOrder_eq_rightOrder]
  ext z
  have hbase :
      codeMap μ (σ : Fin (Fintype.card E) → E) (fun i => (z i).1.1) = base ↔
        ∀ i, (z i).1.1 ∈ GrandCoupling.rawInterval μ
          (σ : Fin (Fintype.card E) → E) base i := by
    have h := Set.ext_iff.mp
      (GrandCoupling.codeMap_fibre_eq_rawbox μ σ base) (fun i => (z i).1.1)
    simpa [Set.mem_pi] using h
  have hleft :
      codeMap μ (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S.leftOrder base (fun i => (z i).1.1)
            (fun i => (z i).1.2)) = left ↔
        ∀ i, causalMixLabels S.leftOrder base (fun i => (z i).1.1)
            (fun i => (z i).1.2) i ∈
          GrandCoupling.rawInterval μ (σ : Fin (Fintype.card E) → E) left i := by
    have h := Set.ext_iff.mp
      (GrandCoupling.codeMap_fibre_eq_rawbox μ σ left)
      (causalMixLabels S.leftOrder base (fun i => (z i).1.1) (fun i => (z i).1.2))
    simpa [Set.mem_pi] using h
  have hright :
      codeMap μ (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S.rightOrder base (fun i => (z i).1.1)
            (fun i => (z i).2)) = right ↔
        ∀ i, causalMixLabels S.rightOrder base (fun i => (z i).1.1)
            (fun i => (z i).2) i ∈
          GrandCoupling.rawInterval μ (σ : Fin (Fintype.card E) → E) right i := by
    have h := Set.ext_iff.mp
      (GrandCoupling.codeMap_fibre_eq_rawbox μ σ right)
      (causalMixLabels S.rightOrder base (fun i => (z i).1.1) (fun i => (z i).2))
    simpa [Set.mem_pi] using h
  simp only [frozenCrossCodeAtom, Set.mem_setOf_eq]
  change
    (codeMap μ (σ : Fin (Fintype.card E) → E) (fun i => (z i).1.1) = base ∧
      codeMap μ (σ : Fin (Fintype.card E) → E)
        (causalMixLabels S.leftOrder base (fun i => (z i).1.1)
          (fun i => (z i).1.2)) = left ∧
      codeMap μ (σ : Fin (Fintype.card E) → E)
        (causalMixLabels S.rightOrder base (fun i => (z i).1.1)
          (fun i => (z i).2)) = right) ↔
      z ∈ Set.univ.pi (crossRawTriple μ S base left right)
  rw [hbase, hleft, hright]
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨hb, hl, hr⟩ i
    specialize hb i
    specialize hl i
    specialize hr i
    cases hm : tripleModeAt S base (σ i) with
    | before =>
        have hl' : (z i).1.2 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) left i := by
          simpa [causalMixLabels, hσ, independentAt_leftOrder, hm,
            TripleMode.leftIndependent] using hl
        have hr' : (z i).2 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) right i := by
          simpa [causalMixLabels, hσ, independentAt_rightOrder, hm,
            TripleMode.rightIndependent, hσr] using hr
        simpa [crossRawTriple, hσ, hm] using ⟨⟨hb, hl'⟩, hr'⟩
    | flip =>
        have hl' : (z i).1.1 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) left i := by
          simpa [causalMixLabels, hσ, independentAt_leftOrder, hm,
            TripleMode.leftIndependent] using hl
        have hr' : (z i).2 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) right i := by
          simpa [causalMixLabels, hσ, independentAt_rightOrder, hm,
            TripleMode.rightIndependent, hσr] using hr
        simpa [crossRawTriple, hσ, hm] using ⟨⟨hb, hl'⟩, hr'⟩
    | after =>
        have hl' : (z i).1.1 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) left i := by
          simpa [causalMixLabels, hσ, independentAt_leftOrder, hm,
            TripleMode.leftIndependent] using hl
        have hr' : (z i).1.1 ∈ GrandCoupling.rawInterval μ (σ :
            Fin (Fintype.card E) → E) right i := by
          simpa [causalMixLabels, hσ, independentAt_rightOrder, hm,
            TripleMode.rightIndependent, hσr] using hr
        simpa [crossRawTriple, hσ, hm] using
          ⟨⟨hb, hl'⟩, hr'⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> intro i
    · specialize h i
      cases hm : tripleModeAt S base (σ i) <;>
        simp only [crossRawTriple, hσ, hm, Set.mem_prod, Set.mem_inter_iff,
          Set.mem_univ, and_true] at h <;> exact h.1.1
    · specialize h i
      cases hm : tripleModeAt S base (σ i) <;>
        simp only [crossRawTriple, hσ, hm, Set.mem_prod, Set.mem_inter_iff,
          Set.mem_univ, and_true] at h <;>
        simpa [causalMixLabels, hσ, independentAt_leftOrder, hm,
          TripleMode.leftIndependent] using h.1.2
    · specialize h i
      cases hm : tripleModeAt S base (σ i) <;>
        simp only [crossRawTriple, hσ, hm, Set.mem_prod, Set.mem_inter_iff,
          Set.mem_univ, and_true] at h <;>
        simpa [causalMixLabels, hσ, independentAt_rightOrder, hm,
          TripleMode.rightIndependent, hσr] using h.2


end AdaptiveCausalKernel
end OSSS
end StatMech
