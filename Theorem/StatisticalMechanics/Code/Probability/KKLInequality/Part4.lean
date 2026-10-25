/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.Poincare.Part2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Def.StatisticalMechanics.Code.Probability.KKLInequality.Part3
open scoped BigOperators
open Finset


namespace StatMech

namespace Probability

open StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem kkl_inequality_total {p c : ℝ} (H : KKLHypercontractive p c)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  H φ


theorem kkl_inequality_max {p c : ℝ} (H : KKLHypercontractive p c)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ (Fintype.card E : ℝ)
          * maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  le_trans (kkl_inequality_total H φ)
    (kkl_maxInfl_ge_avg (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))


theorem kkl_hypercontractive_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    KKLHypercontractive p 0 := by
  intro E _ _ _ φ
  simp only [zero_mul]
  exact kkl_totalInfl_nonneg (bernoulliWeight_isProbWeight hp0 hp1) _


theorem kkl_inequality_total_bernoulli {p c : ℝ} (H : KKLHypercontractive p c)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  kkl_inequality_total H φ


theorem kkl_inequality_max_bernoulli {p c : ℝ} (H : KKLHypercontractive p c)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ (Fintype.card E : ℝ)
          * maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  kkl_inequality_max H φ

end Probability
end StatMech
