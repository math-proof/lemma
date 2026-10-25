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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part17
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


noncomputable def crossTripleWeight (mode : TripleMode) (a q r : ℝ)
    (b y z : Bool) : ℝ :=
  match mode with
  | .before => bitWeight a b * bitWeight q y * bitWeight r z
  | .flip => overlapWeight a q b y * bitWeight r z
  | .after => tripleOverlapWeight a q r b y z


noncomputable def frozenCrossCodeAtom (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    Set (Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ)) :=
  {z | let σ := realizedEquiv S.leftOrder base
       let U := fun i => (z i).1.1
       let V := fun i => (z i).1.2
       let V' := fun i => (z i).2
       codeMap μ (σ : Fin (Fintype.card E) → E) U = base ∧
         codeMap μ (σ : Fin (Fintype.card E) → E)
           (causalMixLabels S.leftOrder base U V) = left ∧
         codeMap μ (σ : Fin (Fintype.card E) → E)
           (causalMixLabels S.rightOrder base U V') = right}


noncomputable def tripleCausalOutputs (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    (Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ)) →
      ConfigSpace E × (ConfigSpace E × ConfigSpace E) := fun z =>
  let σ := realizedEquiv S.leftOrder base
  let U := fun i => (z i).1.1
  let V := fun i => (z i).1.2
  let V' := fun i => (z i).2
  (codeMap μ (σ : Fin (Fintype.card E) → E) U,
    codeMap μ (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.leftOrder base U V),
    codeMap μ (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.rightOrder base U V'))

end AdaptiveCausalKernel
end OSSS
end StatMech
