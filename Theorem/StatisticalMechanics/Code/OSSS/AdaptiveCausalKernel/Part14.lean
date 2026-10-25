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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part14
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


lemma rawInterval_toReal_eq_bitWeight (mu : ConfigSpace E → ℝ)
    (hpos : ∀ omega, 0 < mu omega) {n : ℕ} (sigma : Fin n → E)
    (x : ConfigSpace E) (i : Fin n) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)
      (GrandCoupling.rawInterval mu sigma x i)).toReal =
        bitWeight (thr mu sigma x i) (x (sigma i)) := by
  rw [GrandCoupling.vcube_rawInterval mu hpos sigma x i]
  by_cases hb : x (sigma i)
  · simp only [hb, if_true, bitWeight]
    have hsum := condProbBit_true_add_false mu
      (prefixSet sigma (i : ℕ)) x (sigma i)
      (condNorm_pos hpos _ _).ne'
    change condProbBit mu (prefixSet sigma (i : ℕ)) x (sigma i) true =
      1 - condProbBit mu (prefixSet sigma (i : ℕ)) x (sigma i) false
    linarith
  · simp only [hb, Bool.false_eq_true, if_false, bitWeight]
    rfl


end AdaptiveCausalKernel
end OSSS
end StatMech
