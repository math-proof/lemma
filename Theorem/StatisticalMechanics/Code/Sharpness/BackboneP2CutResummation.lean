/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Def.StatisticalMechanics.Code.Sharpness.BackboneP2CutResummation
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem shb_cutJoin_apply (P : G.edgeFinset → Prop) [DecidablePred P]
    (ab) (e : G.edgeFinset) :
    shb_cutJoin G P ab e = if h : P e then ab.1 ⟨e, h⟩ else ab.2 ⟨e, h⟩ := by
  simp [shb_cutJoin, shb_cutEquiv, Equiv.piEquivPiSubtypeProd]

@[simp] theorem shb_cutLeft_apply (P : G.edgeFinset → Prop) [DecidablePred P]
    (a) (e : G.edgeFinset) :
    shb_cutLeft G P a e = if h : P e then a ⟨e, h⟩ else 0 := by
  simp [shb_cutLeft, shb_cutEquiv, Equiv.piEquivPiSubtypeProd]

@[simp] theorem shb_cutRight_apply (P : G.edgeFinset → Prop) [DecidablePred P]
    (b) (e : G.edgeFinset) :
    shb_cutRight G P b e = if h : P e then 0 else b ⟨e, h⟩ := by
  simp [shb_cutRight, shb_cutEquiv, Equiv.piEquivPiSubtypeProd]


theorem shb_ofEdgeFun_cutJoin_add
    (P : G.edgeFinset → Prop) [DecidablePred P] (a b) :
    (fun e => ofEdgeFun G (shb_cutLeft G P a) e +
      ofEdgeFun G (shb_cutRight G P b) e) =
      ofEdgeFun G (shb_cutJoin G P (a, b)) := by
  funext e
  unfold ofEdgeFun
  by_cases he : e ∈ G.edgeFinset
  · rw [dif_pos he, dif_pos he, dif_pos he]
    by_cases hp : P ⟨e, he⟩ <;> simp [shb_cutJoin_apply, hp]
  · rw [dif_neg he, dif_neg he, dif_neg he]


theorem shb_weight_cutJoin_split (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] (a b) :
    weight G β J (ofEdgeFun G (shb_cutJoin G P (a, b))) =
      weight G β J (ofEdgeFun G (shb_cutLeft G P a)) *
        weight G β J (ofEdgeFun G (shb_cutRight G P b)) := by
  rw [← shb_ofEdgeFun_cutJoin_add G P a b]
  unfold weight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e he => ?_)
  have heSet : e ∈ G.edgeSet := by
    simpa [SimpleGraph.edgeFinset] using he
  unfold ofEdgeFun
  rw [dif_pos he, dif_pos he]
  by_cases hp : P ⟨e, he⟩ <;>
    simp [shb_cutLeft_apply, shb_cutRight_apply, hp, heSet]


theorem shb_cutLeft_injective (P : G.edgeFinset → Prop) [DecidablePred P] :
    Function.Injective (shb_cutLeft G P) := by
  intro a a' h
  have h' := congrArg (shb_cutEquiv G P) h
  simpa [shb_cutLeft] using congrArg Prod.fst h'

theorem shb_cutRight_injective (P : G.edgeFinset → Prop) [DecidablePred P] :
    Function.Injective (shb_cutRight G P) := by
  intro b b' h
  have h' := congrArg (shb_cutEquiv G P) h
  simpa [shb_cutRight] using congrArg Prod.snd h'

end StatMech.Sharpness
