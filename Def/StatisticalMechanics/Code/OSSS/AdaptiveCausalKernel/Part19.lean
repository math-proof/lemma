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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part18
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


noncomputable def crossRawTriple (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) (i : Fin (Fintype.card E)) :
    Set ((ℝ × ℝ) × ℝ) :=
  let σ := realizedEquiv S.leftOrder base
  let A := GrandCoupling.rawInterval μ (σ : Fin (Fintype.card E) → E) base i
  let B := GrandCoupling.rawInterval μ (σ : Fin (Fintype.card E) → E) left i
  let C := GrandCoupling.rawInterval μ (σ : Fin (Fintype.card E) → E) right i
  match tripleModeAt S base (σ i) with
  | .before => (A ×ˢ B) ×ˢ C
  | .flip => ((A ∩ B) ×ˢ Set.univ) ×ˢ C
  | .after => ((A ∩ B ∩ C) ×ˢ Set.univ) ×ˢ Set.univ

end AdaptiveCausalKernel
end OSSS
end StatMech
