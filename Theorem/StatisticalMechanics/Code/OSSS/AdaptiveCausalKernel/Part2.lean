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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part2
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


lemma realizedEquiv_symm_val
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E) (e : E) :
    ((realizedEquiv S base).symm e : ℕ) = (realizedList S base).idxOf e := by
  unfold realizedEquiv
  simp [List.Nodup.getEquivOfForallMemList]


lemma prefixSet_realizedEquiv (S : CausalOrder (Finset.univ : Finset E))
    (base : ConfigSpace E) (e : E) :
    prefixSet (realizedEquiv S base : Fin (Fintype.card E) → E)
        ((realizedEquiv S base).symm e : ℕ) =
      ((realizedList S base).take ((realizedList S base).idxOf e)).toFinset := by
  ext z
  have hze : z ∈ realizedList S base := by
    rw [← List.mem_toFinset, realizedList_toFinset]
    exact Finset.mem_univ z
  rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt hze]
  rw [mem_prefixSet_iff]
  constructor
  · rintro ⟨j, hj, hjz⟩
    have hpos : j = ((realizedEquiv S base).symm z : Fin (Fintype.card E)) :=
      (realizedEquiv S base).injective (by simpa using hjz)
    subst j
    simpa only [realizedEquiv_symm_val] using hj
  · intro hj
    refine ⟨(realizedEquiv S base).symm z, ?_, by simp⟩
    simpa only [realizedEquiv_symm_val] using hj

lemma thr_realizedEquiv (μ : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E)) (base target : ConfigSpace E) (e : E) :
    thr μ (realizedEquiv S base : Fin (Fintype.card E) → E) target
        ((realizedEquiv S base).symm e) =
      condProbClosed μ
        ((realizedList S base).take ((realizedList S base).idxOf e)).toFinset
        target e := by
  unfold thr
  rw [prefixSet_realizedEquiv, Equiv.apply_symm_apply]


end AdaptiveCausalKernel
end OSSS
end StatMech
