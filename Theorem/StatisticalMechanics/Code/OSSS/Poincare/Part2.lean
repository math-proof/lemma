/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Def.StatisticalMechanics.Code.OSSS.Poincare.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace Poincare

open DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma eval_fullTreeUniv (φ : ConfigSpace E → Bool) (ω : ConfigSpace E) :
    (fullTreeUniv φ).eval ω = φ ω := by
  apply eval_fullTree
  intro a b hab
  congr 1
  funext e
  exact hab e (by simp)


lemma evalR_fullTreeUniv (φ : ConfigSpace E → Bool) (ω : ConfigSpace E) :
    (fullTreeUniv φ).evalR ω = if φ ω then (1 : ℝ) else 0 := by
  unfold DecisionTree.evalR
  rw [eval_fullTreeUniv]


lemma mem_queried_fullTreeUniv (e : E) (φ : ConfigSpace E → Bool) (ω : ConfigSpace E) :
    e ∈ (fullTreeUniv φ).queried ω :=
  mem_queried_fullTree e φ _ (by simp) ω


lemma reveal_fullTreeUniv {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (φ : ConfigSpace E → Bool) (e : E) :
    reveal ν (fullTreeUniv φ) e = 1 := by
  unfold reveal
  have hone : (fun ω => if e ∈ (fullTreeUniv φ).queried ω then (1 : ℝ) else 0)
      = (fun _ => (1 : ℝ)) := by
    funext ω
    rw [if_pos (mem_queried_fullTreeUniv e φ ω)]
  rw [hone, expect_one hν]


theorem poincare {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (φ : ConfigSpace E → Bool) :
    var ν (fun ω => if φ ω then (1 : ℝ) else 0)
      ≤ ∑ e, infl ν (fun ω => if φ ω then (1 : ℝ) else 0) e := by
  
  have hfun : (fun ω => if φ ω then (1 : ℝ) else 0) = (fullTreeUniv φ).evalR := by
    funext ω; rw [evalR_fullTreeUniv]
  rw [hfun]
  
  refine (osss_var hν (fullTreeUniv φ)).trans ?_
  
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro e _
  rw [reveal_fullTreeUniv hν φ e, one_mul]


theorem poincare_cov {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (φ : ConfigSpace E → Bool)
    (g : ConfigSpace E → ℝ) :
    cov ν (fun ω => if φ ω then (1 : ℝ) else 0) g ≤ ∑ e, infl ν g e := by
  have hfun : (fun ω => if φ ω then (1 : ℝ) else 0) = (fullTreeUniv φ).evalR := by
    funext ω; rw [evalR_fullTreeUniv]
  rw [hfun]
  refine (osss hν (fullTreeUniv φ) g).trans ?_
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro e _
  rw [reveal_fullTreeUniv hν φ e, one_mul]


theorem poincare_bernoulli {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (φ : ConfigSpace E → Bool) :
    var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      ≤ ∑ e, infl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e :=
  poincare (bernoulliWeight_isProbWeight hp0 hp1) φ

end Poincare
end OSSS
end StatMech
