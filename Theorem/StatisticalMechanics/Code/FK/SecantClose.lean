/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.PressureDiff
import Theorem.StatisticalMechanics.Code.FK.TiltSecant.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
import Def.StatisticalMechanics.Code.FK.SecantClose
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


theorem fsc_logistic_pos (t : ℝ) : 0 < fsc_logistic t := by
  unfold fsc_logistic; positivity


theorem fsc_logistic_lt_one (t : ℝ) : fsc_logistic t < 1 := by
  unfold fsc_logistic
  rw [div_lt_one (by positivity)]
  have := Real.exp_pos t; linarith


theorem fsc_logistic_mem_Ioo (t : ℝ) : fsc_logistic t ∈ Ioo (0 : ℝ) 1 :=
  ⟨fsc_logistic_pos t, fsc_logistic_lt_one t⟩


theorem fsc_logistic_strictMono : StrictMono fsc_logistic := by
  intro a b hab
  unfold fsc_logistic
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h1 := Real.exp_pos a
  have h2 := Real.exp_pos b
  have he : Real.exp a < Real.exp b := Real.exp_lt_exp.mpr hab
  nlinarith [he, h1, h2]


theorem fsc_logistic_logit {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    fsc_logistic (fsc_logit p) = p := by
  unfold fsc_logistic fsc_logit
  have h1mp : 0 < 1 - p := by linarith
  rw [Real.exp_log (by positivity)]
  field_simp
  ring


end FK
end StatMech
