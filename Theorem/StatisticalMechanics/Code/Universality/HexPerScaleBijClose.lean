/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexPerScaleBijClose


namespace StatMech.Universality

open scoped BigOperators

open Filter Topology


theorem hpb_tsum_setDiff (P Q : List ℤ → Prop) (w : List ℤ → ℝ)
    (hsub : ∀ ts, Q ts → P ts)
    (hsumP : Summable (fun n : {ts // P ts} => w n.1)) :
    (∑' d : {ts // P ts ∧ ¬ Q ts}, w d.1)
      = (∑' n : {ts // P ts}, w n.1) - (∑' n : {ts // Q ts}, w n.1) := by
  classical
  set g : ({ts // Q ts} ⊕ {ts // P ts ∧ ¬ Q ts}) → ℝ :=
    Sum.elim (fun q => w q.1) (fun d => w d.1) with hg
  have hcongr : ∀ x : {ts // P ts}, w x.1 = g (hpb_splitEquiv P Q hsub x) := by
    intro x
    change w x.1 = g (if h : Q x.1 then Sum.inl ⟨x.1, h⟩ else Sum.inr ⟨x.1, x.2, h⟩)
    by_cases h : Q x.1 <;> simp [h, hg]
  have hsumG : Summable g := by
    have : Summable (fun x : {ts // P ts} => g (hpb_splitEquiv P Q hsub x)) :=
      hsumP.congr (fun x => hcongr x)
    exact ((hpb_splitEquiv P Q hsub).summable_iff (f := g)).mp this
  have hsumQ : Summable (fun q : {ts // Q ts} => w q.1) :=
    hsumG.comp_injective Sum.inl_injective
  have hsumD : Summable (fun d : {ts // P ts ∧ ¬ Q ts} => w d.1) :=
    hsumG.comp_injective Sum.inr_injective
  have key : (∑' n : {ts // P ts}, w n.1)
      = (∑' q : {ts // Q ts}, w q.1) + (∑' d : {ts // P ts ∧ ¬ Q ts}, w d.1) := by
    have h1 : (∑' n : {ts // P ts}, w n.1) = ∑' s, g s := by
      rw [← (hpb_splitEquiv P Q hsub).tsum_eq g]; exact tsum_congr hcongr
    rw [h1]; exact (HasSum.sum hsumQ.hasSum hsumD.hasSum).tsum_eq
  linarith [key]


end StatMech.Universality
