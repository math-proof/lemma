/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem KWStraightLineEmbedding.outgoing_dartAngle_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {d e : G.Dart}
    (hfst : d.fst = e.fst) (hne : d ≠ e) :
    embedding.dartAngle d ≠ embedding.dartAngle e := by
  have hedge : d.edge ≠ e.edge := by
    intro h
    rw [SimpleGraph.dart_edge_eq_iff] at h
    rcases h with h | h
    · exact hne h
    · have := congrArg (fun delta : G.Dart ↦ delta.fst) h
      apply e.fst_ne_snd
      simpa [hfst] using this.symm
  have hadj : G.DartAdj d.symm e := by
    change d.symm.snd = e.fst
    simp [hfst]
  have hnon := embedding.nonantipodal_of_nonbacktracking d.symm e hadj (by
    simpa using hedge)
  intro hangle
  apply hnon
  rw [embedding.dartAngle_symm, ← hangle]
  simp


theorem kwAngularPortOrder_rank_lt_of_angle_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {p q : KWDartPort G}
    (hfst : p.1 = q.1)
    (hangle : (embedding.dartAngle (kwDartOfPort G p)).toReal <
      (embedding.dartAngle (kwDartOfPort G q)).toReal) :
    kwOrderedPortRank (kwAngularPortOrder embedding) p <
      kwOrderedPortRank (kwAngularPortOrder embedding) q := by
  rcases p with ⟨v, i⟩
  rcases q with ⟨w, j⟩
  dsimp only at hfst ⊢
  subst w
  let outgoing := KWOutgoingDart (G := G) v
  let key : outgoing → ℝ ×ₗ ℕ := fun d ↦
    toLex ((embedding.dartAngle d.1).toReal,
      (Fintype.equivFin outgoing d).val)
  have hkey : Function.Injective key := by
    intro d e h
    apply (Fintype.equivFin outgoing).injective
    apply Fin.ext
    exact congrArg (fun z ↦ (ofLex z).2) h
  letI : LinearOrder outgoing := LinearOrder.lift' key hkey
  let oi := Fintype.orderIsoFinOfCardEq outgoing rfl
  have hdart :
      (Fintype.equivFin outgoing).symm i <
        (Fintype.equivFin outgoing).symm j := by
    change key ((Fintype.equivFin outgoing).symm i) <
      key ((Fintype.equivFin outgoing).symm j)
    rw [Prod.Lex.toLex_lt_toLex]
    left
    simpa only [outgoing, key, kwDartOfPort, kwDartPortEquiv] using hangle
  change (oi.symm ((Fintype.equivFin outgoing).symm i)).val <
    (oi.symm ((Fintype.equivFin outgoing).symm j)).val
  exact (oi.symm.lt_iff_lt).2 hdart

theorem kwAngularPortOrder_rank_lt_iff_angle_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {p q : KWDartPort G}
    (hfst : p.1 = q.1) :
    kwOrderedPortRank (kwAngularPortOrder embedding) p <
        kwOrderedPortRank (kwAngularPortOrder embedding) q ↔
      (embedding.dartAngle (kwDartOfPort G p)).toReal <
        (embedding.dartAngle (kwDartOfPort G q)).toReal := by
  constructor
  · intro hrank
    have hpq : p ≠ q := by
      intro h
      subst q
      omega
    have hdart : kwDartOfPort G p ≠ kwDartOfPort G q :=
      (kwDartOfPort_injective G).ne hpq
    have hangle := embedding.outgoing_dartAngle_ne
      (kwDartOfPort_fst G p |>.trans (hfst.trans (kwDartOfPort_fst G q).symm))
      hdart
    have hreal : (embedding.dartAngle (kwDartOfPort G p)).toReal ≠
        (embedding.dartAngle (kwDartOfPort G q)).toReal := by
      intro h
      apply hangle
      rw [← Real.Angle.coe_toReal (embedding.dartAngle (kwDartOfPort G p)),
        ← Real.Angle.coe_toReal (embedding.dartAngle (kwDartOfPort G q)), h]
    rcases lt_or_gt_of_ne hreal with hlt | hgt
    · exact hlt
    · have hreverse := kwAngularPortOrder_rank_lt_of_angle_lt embedding
          hfst.symm hgt
      omega
  · exact kwAngularPortOrder_rank_lt_of_angle_lt embedding hfst


theorem kw_oppositeTurn_toReal_of_lt (a b : Real.Angle)
    (h : a.toReal < b.toReal) :
    (b - (a + (Real.pi : Real.Angle))).toReal =
      b.toReal - a.toReal - Real.pi := by
  have hcoe : ((b.toReal - a.toReal - Real.pi : ℝ) : Real.Angle) =
      b - (a + (Real.pi : Real.Angle)) := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_sub,
      Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    abel
  rw [← hcoe]
  apply Real.Angle.toReal_coe_eq_self_iff.mpr
  constructor
  · linarith
  · nlinarith [Real.Angle.neg_pi_lt_toReal a,
      Real.Angle.toReal_le_pi b, Real.pi_pos]


theorem kw_oppositeTurn_toReal_of_gt (a b : Real.Angle)
    (h : b.toReal < a.toReal) :
    (b - (a + (Real.pi : Real.Angle))).toReal =
      b.toReal - a.toReal + Real.pi := by
  have hcoe : ((b.toReal - a.toReal + Real.pi : ℝ) : Real.Angle) =
      b - (a + (Real.pi : Real.Angle)) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_sub,
      Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    rw [← Real.Angle.sub_coe_pi_eq_add_coe_pi]
    abel
  rw [← hcoe]
  apply Real.Angle.toReal_coe_eq_self_iff.mpr
  constructor
  · nlinarith [Real.Angle.neg_pi_lt_toReal b,
      Real.Angle.toReal_le_pi a, Real.pi_pos]
  · linarith


end StatMech.FrontierA
