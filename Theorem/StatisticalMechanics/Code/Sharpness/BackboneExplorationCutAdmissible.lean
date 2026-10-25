/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem shb_summable_cutLeftPredicate
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (left : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred left] :
    Summable (fun a =>
      if left a then shb_cutLeftWeight G beta J P a else 0) := by
  let f := fun a => shb_cutLeftWeight G beta J P a
  have hf : Summable f := shb_summable_weight_cutLeft G beta J P
  have heq : (fun a => if left a then f a else 0) =
      Set.indicator {a | left a} f := by
    funext a
    by_cases ha : left a <;> simp [Set.indicator, ha]
  rw [heq]
  exact hf.indicator _

theorem shb_summable_cutRightPredicate
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (right : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred right] :
    Summable (fun b =>
      if right b then shb_cutRightWeight G beta J P b else 0) := by
  let f := fun b => shb_cutRightWeight G beta J P b
  have hf : Summable f := shb_summable_weight_cutRight G beta J P
  have heq : (fun b => if right b then f b else 0) =
      Set.indicator {b | right b} f := by
    funext b
    by_cases hb : right b <;> simp [Set.indicator, hb]
  rw [heq]
  exact hf.indicator _


theorem shb_cutPredicateMass_factor
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (full : (G.edgeFinset -> Nat) -> Prop) [DecidablePred full]
    (left : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred left]
    (right : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred right]
    (hadm : shb_CutPredicateAdmissible G P full left right) :
    shb_cutFullPredicateMass G beta J full =
      shb_cutLeftPredicateMass G beta J P left *
        shb_cutRightPredicateMass G beta J P right := by
  unfold shb_cutFullPredicateMass shb_cutLeftPredicateMass
    shb_cutRightPredicateMass
  rw [← (shb_cutEquiv G P).symm.tsum_eq]
  rw [tsum_congr (fun ab => ?_)]
  · exact shb_tsum_prod_factor
      (fun a => if left a then shb_cutLeftWeight G beta J P a else 0)
      (fun b => if right b then shb_cutRightWeight G beta J P b else 0)
      (shb_summable_cutLeftPredicate G beta J P left)
      (shb_summable_cutRightPredicate G beta J P right)
  · change (if full (shb_cutJoin G P ab) then
        weight G beta J (ofEdgeFun G (shb_cutJoin G P ab)) else 0) =
      (if left ab.1 then
          weight G beta J (ofEdgeFun G (shb_cutLeft G P ab.1)) else 0) *
        (if right ab.2 then
          weight G beta J (ofEdgeFun G (shb_cutRight G P ab.2)) else 0)
    rw [shb_weight_cutJoin_split]
    by_cases ha : left ab.1 <;> by_cases hb : right ab.2
    · rw [if_pos ((hadm ab.1 ab.2).2 ⟨ha, hb⟩), if_pos ha, if_pos hb]
    · rw [if_neg (fun h => hb ((hadm ab.1 ab.2).1 h).2), if_pos ha,
        if_neg hb, mul_zero]
    · rw [if_neg (fun h => ha ((hadm ab.1 ab.2).1 h).1), if_neg ha,
        if_pos hb, zero_mul]
    · rw [if_neg (fun h => ha ((hadm ab.1 ab.2).1 h).1), if_neg ha,
        if_neg hb, zero_mul]


theorem shb_sources_cutJoin
    (P : G.edgeFinset -> Prop) [DecidablePred P] (a b) :
    sources G (ofEdgeFun G (shb_cutJoin G P (a, b))) =
      sources G (ofEdgeFun G (shb_cutLeft G P a)) ∆
        sources G (ofEdgeFun G (shb_cutRight G P b)) := by
  rw [← shb_ofEdgeFun_cutJoin_add G P a b]
  exact sources_add G (ofEdgeFun G (shb_cutLeft G P a))
    (ofEdgeFun G (shb_cutRight G P b))


end
end StatMech.Sharpness
