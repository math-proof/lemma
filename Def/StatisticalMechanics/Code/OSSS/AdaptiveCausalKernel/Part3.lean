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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part2
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


def independentAt : {R : Finset E} → CausalOrder R →
    ConfigSpace E → E → Bool
  | _, .done, _, _ => false
  | _, .node e _ independent closed opened, base, z =>
      if z = e then independent
      else if base e then independentAt opened base z
      else independentAt closed base z


noncomputable def causalMixLabels
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) : Fin (Fintype.card E) → ℝ :=
  fun i => if independentAt S base (realizedEquiv S base i) then V i else U i


noncomputable def frozenCodeAtom (mu : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) :
    Set (Fin (Fintype.card E) → (ℝ × ℝ)) :=
  {z | let sigma := realizedEquiv S base
       let U := fun i => (z i).1
       let V := fun i => (z i).2
       codeMap mu (sigma : Fin (Fintype.card E) → E) U = base ∧
         codeMap mu (sigma : Fin (Fintype.card E) → E)
           (causalMixLabels S base U V) = target}


noncomputable def frozenRawPair (mu : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) (i : Fin (Fintype.card E)) : Set (ℝ × ℝ) :=
  let sigma := realizedEquiv S base
  let A := StatMech.OSSS.GrandCoupling.rawInterval mu
    (sigma : Fin (Fintype.card E) → E) base i
  let B := StatMech.OSSS.GrandCoupling.rawInterval mu
    (sigma : Fin (Fintype.card E) → E) target i
  if independentAt S base (sigma i) then A ×ˢ B else (A ∩ B) ×ˢ Set.univ


end AdaptiveCausalKernel
end OSSS
end StatMech
