/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Def.StatisticalMechanics.Code.Sharpness.BackboneP2CutResummation.Part2
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem shb_cutJoinWeight_factor (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] (ab) :
    shb_cutJoinWeight G β J P ab =
      shb_cutLeftWeight G β J P ab.1 * shb_cutRightWeight G β J P ab.2 := by
  exact shb_weight_cutJoin_split G β J P ab.1 ab.2


theorem shb_summable_weight_cutLeft (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    Summable (fun a : {e : G.edgeFinset // P e} → ℕ =>
      shb_cutLeftWeight G β J P a) :=
  (shb_summable_weight G β J).comp_injective (shb_cutLeft_injective G P)

theorem shb_summable_weight_cutRight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    Summable (fun b : {e : G.edgeFinset // ¬ P e} → ℕ =>
      shb_cutRightWeight G β J P b) :=
  (shb_summable_weight G β J).comp_injective (shb_cutRight_injective G P)

theorem shb_tsum_prod_factor {A B : Type*} (f : A → ℝ) (g : B → ℝ)
    (hf : Summable f) (hg : Summable g) :
    (∑' ab : A × B, f ab.1 * g ab.2) = (∑' a, f a) * ∑' b, g b := by
  exact (Summable.tsum_mul_tsum hf hg
    (summable_mul_of_summable_norm hf.norm hg.norm)).symm


end StatMech.Sharpness
