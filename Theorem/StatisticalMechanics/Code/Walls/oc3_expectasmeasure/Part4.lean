/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.Walls.oc3_vcubeprob
import Def.StatisticalMechanics.Code.Walls.oc3_expectasmeasure.Part3
open scoped BigOperators ENNReal
open Finset MeasureTheory
open StatMech.OSSS

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Walls

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc3_bernoulliWeight_isProb {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbWeight (oc3_bernoulliWeight (E := E) p) where
  nonneg := by
    intro e b
    cases b <;> simp only [oc3_bernoulliWeight, Bool.false_eq_true, if_false, if_true] <;>
      linarith
  normalized := by
    intro e
    simp only [oc3_bernoulliWeight, Bool.false_eq_true, if_false, if_true]
    ring


theorem oc3_expect_eq_integral_bernoulli {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : ConfigSpace E → ℝ) :
    expect (oc3_bernoulliWeight (E := E) p) g
      = ∫ ω, g ω ∂(oc3_pwMeasure (oc3_bernoulliWeight (E := E) p)
          (oc3_bernoulliWeight_isProb hp0 hp1)) :=
  oc3_expect_eq_integral _ (oc3_bernoulliWeight_isProb hp0 hp1) g


section FK

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem oc3_fk_expect_eq_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    expect (oc3_bernoulliWeight (E := Sym2 V) p) g
      = ∫ ω, g ω ∂(oc3_pwMeasure (oc3_bernoulliWeight (E := Sym2 V) p)
          (oc3_bernoulliWeight_isProb hp0 hp1)) :=
  oc3_expect_eq_integral _ (oc3_bernoulliWeight_isProb hp0 hp1) g

end FK


theorem oc3_vcubeProb_dep (n : ℕ) :
    IsProbabilityMeasure (StatMech.OSSS.GrandCoupling.Vcube n) :=
  oc3_vcube_isProbabilityMeasure n

end Walls
end StatMech
