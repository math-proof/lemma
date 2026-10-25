/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.KKLWire.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.KKLpBiased
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Probability

open ConfigSpace Function Finset StatMech StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] [DecidableEq E] in

lemma kpb_flipAll_involutive : Function.Involutive (kpb_flipAll (E := E)) := by
  intro ω; funext e; simp [kpb_flipAll]

omit [DecidableEq E] in


lemma kpb_weight_flip (p : ℝ) (ω : ConfigSpace E) :
    OSSS.weight (OSSS.bernoulliWeight (1 - p)) (kpb_flipAll ω)
      = OSSS.weight (OSSS.bernoulliWeight p) ω := by
  unfold OSSS.weight OSSS.bernoulliWeight kpb_flipAll
  apply Finset.prod_congr rfl
  intro e _
  cases ω e <;> simp


lemma kpb_expect_flip (p : ℝ) (g : ConfigSpace E → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight (1 - p)) g
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold OSSS.expect
  rw [Fintype.sum_bijective (kpb_flipAll) (kpb_flipAll_involutive.bijective)
        (fun ω => OSSS.weight (OSSS.bernoulliWeight p) ω * g (kpb_flipAll ω))
        (fun ω => OSSS.weight (OSSS.bernoulliWeight (1 - p)) ω * g ω)
        (fun ω => by simp only [kpb_weight_flip])]

omit [Fintype E] in

lemma kpb_flipAll_setOpen (e : E) (ω : ConfigSpace E) :
    kpb_flipAll (StatMech.setOpen e ω) = StatMech.setClosed e (kpb_flipAll ω) := by
  funext e'; unfold kpb_flipAll StatMech.setOpen StatMech.setClosed
  by_cases h : e' = e
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]

omit [Fintype E] in

lemma kpb_flipAll_setClosed (e : E) (ω : ConfigSpace E) :
    kpb_flipAll (StatMech.setClosed e ω) = StatMech.setOpen e (kpb_flipAll ω) := by
  funext e'; unfold kpb_flipAll StatMech.setOpen StatMech.setClosed
  by_cases h : e' = e
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]


lemma kpb_infl_flip (p : ℝ) (g : ConfigSpace E → ℝ) (e : E) :
    OSSS.infl (OSSS.bernoulliWeight (1 - p)) g e
      = OSSS.infl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) e := by
  unfold OSSS.infl
  rw [kpb_expect_flip p]
  apply congrArg
  funext ω
  simp only [kpb_flipAll_setOpen, kpb_flipAll_setClosed]
  rw [abs_sub_comm]


lemma kpb_var_flip (p : ℝ) (g : ConfigSpace E → ℝ) :
    OSSS.var (OSSS.bernoulliWeight (1 - p)) g
      = OSSS.var (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold OSSS.var OSSS.cov
  rw [kpb_expect_flip p (fun ω => g ω * g ω), kpb_expect_flip p g]


lemma kpb_totalInfl_flip (p : ℝ) (g : ConfigSpace E → ℝ) :
    totalInfl (OSSS.bernoulliWeight (1 - p)) g
      = totalInfl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold totalInfl
  exact Finset.sum_congr rfl (fun e _ => kpb_infl_flip p g e)


lemma kpb_maxInfl_flip [Nonempty E] (p : ℝ) (g : ConfigSpace E → ℝ) :
    maxInfl (OSSS.bernoulliWeight (1 - p)) g
      = maxInfl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold maxInfl
  apply Finset.sup'_congr _ rfl
  intro e _
  exact kpb_infl_flip p g e


theorem kpb_kkl_reflect {p : ℝ} (H : KKLHypercontractive p 2) :
    KKLHypercontractive (1 - p) 2 := by
  intro E _ _ _ φ
  
  have hH := H (E := E) (fun ω => φ (kpb_flipAll ω))
  have he : (fun ω => if φ (kpb_flipAll ω) then (1 : ℝ) else 0)
      = (fun ω => (fun ω => if φ ω then (1 : ℝ) else 0) (kpb_flipAll ω)) := rfl
  rw [he] at hH
  rw [kpb_var_flip p, kpb_maxInfl_flip p, kpb_totalInfl_flip p]
  exact hH


end Probability
end StatMech
