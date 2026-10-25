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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part20
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


noncomputable def tripleLabelCube (n : ℕ) : Measure (Fin n → ((ℝ × ℝ) × ℝ)) :=
  Measure.pi fun _ =>
    ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Icc (0 : ℝ) 1))).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))

noncomputable def frozenCrossRawAtom (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) : Set (Fin (Fintype.card E) → ((ℝ × ℝ) × ℝ)) :=
  Set.univ.pi (crossRawTriple μ S base left right)

end AdaptiveCausalKernel
end OSSS
end StatMech
