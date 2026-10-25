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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part7
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


theorem frozenTripleCodeAtom_eq_rawPairBox (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    frozenTripleCodeAtom mu S base left right =
      Set.univ.pi (frozenTripleRawPair mu S base left right) := by
  unfold frozenTripleCodeAtom
  rw [frozenCodeAtom_eq_rawPairBox mu S.leftOrder base left]
  rw [frozenCodeAtom_eq_rawPairBox mu S.rightOrder base right]
  ext z
  simp only [frozenTripleRawPair, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
    true_implies]
  constructor
  · rintro ⟨hl, hr⟩ i
    exact ⟨hl i, hr i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem pairedCube_frozenTripleCodeAtom (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    pairedCube (Fintype.card E) (frozenTripleCodeAtom mu S base left right) =
      ∏ i : Fin (Fintype.card E),
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1)))
            (frozenTripleRawPair mu S base left right i) := by
  rw [frozenTripleCodeAtom_eq_rawPairBox, pairedCube, Measure.pi_pi]


end AdaptiveCausalKernel
end OSSS
end StatMech
