/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortEmbedding.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngularPortPhase.Part3


namespace StatMech.FrontierA

open SimpleGraph

theorem KWAngularPortRadiusData.phaseGauge_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    data.phaseGauge d ≠ 0 := by
  unfold KWAngularPortRadiusData.phaseGauge
  split
  · norm_num
  · exact kwRawDirectionRoot_ne_zero _

theorem portAngle_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (p : KWDartPort G) :
    -Real.pi < (embedding.dartAngle (kwDartOfPort G p)).toReal ∧
      (embedding.dartAngle (kwDartOfPort G p)).toReal ≤ Real.pi :=
  ⟨Real.Angle.neg_pi_lt_toReal _, Real.Angle.toReal_le_pi _⟩

theorem external_raw_angle_eq_at_snd
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm) :
    (data.rawDartDirection d : Real.Angle) =
      (embedding.dartAngle (kwDartOfPort G d.snd) +
        (Real.pi : Real.Angle)) := by
  simp only [KWAngularPortRadiusData.rawDartDirection, hd, if_pos]
  rw [embedding.dartAngle_symm]
  simp only [Real.Angle.coe_toReal]
  rw [add_assoc, ← Real.Angle.coe_add]
  simp

theorem external_raw_angle_eq_at_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm) :
    (data.rawDartDirection d : Real.Angle) =
      embedding.dartAngle (kwDartOfPort G d.fst) := by
  simp [KWAngularPortRadiusData.rawDartDirection, hd]


theorem KWAngularPortRadiusData.realizedTurnPhase_eq_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hconnect : d.snd = e.fst) (hne : d.edge ≠ e.edge) :
    data.toStraightLineEmbedding.turnPhase d e =
      kwPhaseGauge data.phaseGauge (kwAngularSplitPhase embedding) d e := by
  rw [data.realizedTurnPhase_eq_raw]
  unfold kwPhaseGauge
  by_cases hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
    · exfalso
      apply hne
      have hsnd : e.snd = d.fst := by
        apply kwDartOfPort_injective G
        rw [he, ← hconnect, hd]
        simp
      have hedart : e = d.symm := by
        apply SimpleGraph.Dart.ext
        exact Prod.ext hconnect.symm hsnd
      rw [hedart]
      exact d.edge_symm.symm
    · have edata := (kwOrderedDartPortSplitGraph_adj G
          (kwAngularPortOrder embedding) e.fst e.snd).mp e.adj |>.resolve_left he
      let a := (embedding.dartAngle (kwDartOfPort G e.fst)).toReal
      let b := (embedding.dartAngle (kwDartOfPort G e.snd)).toReal
      have habBounds := portAngle_bounds embedding e.fst
      have hbbounds := portAngle_bounds embedding e.snd
      have hdRawPlus : (data.rawDartDirection d : Real.Angle) =
          ((a + Real.pi : ℝ) : Real.Angle) := by
        calc
          _ = embedding.dartAngle (kwDartOfPort G d.snd) +
              (Real.pi : Real.Angle) := external_raw_angle_eq_at_snd data d hd
          _ = embedding.dartAngle (kwDartOfPort G e.fst) +
              (Real.pi : Real.Angle) := by rw [hconnect]
          _ = ((a + Real.pi : ℝ) : Real.Angle) := by
            simp only [a, Real.Angle.coe_add, Real.Angle.coe_toReal]
      have hdRawMinus : (data.rawDartDirection d : Real.Angle) =
          ((a - Real.pi : ℝ) : Real.Angle) := by
        rw [hdRawPlus]
        change (a : Real.Angle) + (Real.pi : Real.Angle) =
          (a : Real.Angle) - (Real.pi : Real.Angle)
        rw [sub_eq_add_neg, Real.Angle.neg_coe_pi]
      by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) e.snd
      · have hab : a < b :=
          (kwAngularPortOrder_rank_lt_iff_angle_lt embedding edata.1).mp hinc
        have heRaw : data.rawDartDirection e =
            (a + b) / 2 + Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, he, hinc, a, b]
        rw [hdRawPlus, heRaw,
          kwAngleTurnPhase_coe_eq_rootRatio]
        · simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc]
          rw [kwPortAngleRoot_eq_rawDirectionRoot,
            kwRawDirectionRoot_add_pi_inv]
          simp only [a, b]
          ring
        · nlinarith [habBounds.1, hbbounds.2, Real.pi_pos]
        · nlinarith [habBounds.1, hbbounds.2, Real.pi_pos]
      · have hdec : kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := by
          rcases edata.2 with h | h <;> omega
        have hba : b < a :=
          (kwAngularPortOrder_rank_lt_iff_angle_lt embedding edata.1.symm).mp hdec
        have heRaw : data.rawDartDirection e =
            (a + b) / 2 - Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, he, hinc, a, b]
        rw [hdRawMinus, heRaw,
          kwAngleTurnPhase_coe_eq_rootRatio]
        · simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc]
          rw [kwPortAngleRoot_eq_rawDirectionRoot,
            kwRawDirectionRoot_sub_pi_inv]
        · nlinarith [hbbounds.1, habBounds.2, Real.pi_pos]
        · nlinarith [hbbounds.1, habBounds.2, Real.pi_pos]
  · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
    · have ddata := (kwOrderedDartPortSplitGraph_adj G
          (kwAngularPortOrder embedding) d.fst d.snd).mp d.adj |>.resolve_left hd
      let a := (embedding.dartAngle (kwDartOfPort G d.fst)).toReal
      let b := (embedding.dartAngle (kwDartOfPort G d.snd)).toReal
      have habBounds := portAngle_bounds embedding d.fst
      have hbbounds := portAngle_bounds embedding d.snd
      have heRaw : (data.rawDartDirection e : Real.Angle) =
          (b : Real.Angle) := by
        calc
          _ = embedding.dartAngle (kwDartOfPort G e.fst) :=
            external_raw_angle_eq_at_fst data e he
          _ = embedding.dartAngle (kwDartOfPort G d.snd) := by rw [← hconnect]
          _ = (b : Real.Angle) := by simp only [b, Real.Angle.coe_toReal]
      by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
      · have hab : a < b :=
          (kwAngularPortOrder_rank_lt_iff_angle_lt embedding ddata.1).mp hinc
        have hdRaw : data.rawDartDirection d =
            (a + b) / 2 + Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
        rw [hdRaw, heRaw, kwAngleTurnPhase_coe_eq_rootRatio]
        · simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc]
          rw [kwPortAngleRoot_eq_rawDirectionRoot]
          simp only [← hconnect, b]
          simp only [a]
        · nlinarith [habBounds.1, hbbounds.2, Real.pi_pos]
        · nlinarith [habBounds.1, hbbounds.2, Real.pi_pos]
      · have hdec : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
          rcases ddata.2 with h | h <;> omega
        have hba : b < a :=
          (kwAngularPortOrder_rank_lt_iff_angle_lt embedding ddata.1.symm).mp hdec
        have hdRaw : data.rawDartDirection d =
            (a + b) / 2 - Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
        rw [hdRaw, heRaw, kwAngleTurnPhase_coe_eq_rootRatio]
        · simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc]
          rw [kwPortAngleRoot_eq_rawDirectionRoot]
          simp only [← hconnect, b]
          simp only [a]
        · nlinarith [hbbounds.1, habBounds.2, Real.pi_pos]
        · nlinarith [hbbounds.1, habBounds.2, Real.pi_pos]
    · let di : KWOrderedInternalSplitDart G
          (kwAngularPortOrder embedding) := ⟨d, hd⟩
      let ei : KWOrderedInternalSplitDart G
          (kwAngularPortOrder embedding) := ⟨e, he⟩
      have hstep : KWOrderedInternalDartStep G
          (kwAngularPortOrder embedding) di ei := ⟨hconnect, hne⟩
      have ddata' := kwOrderedInternalSplitDart_adj_data G
        (kwAngularPortOrder embedding) di
      have edata' := kwOrderedInternalSplitDart_adj_data G
        (kwAngularPortOrder embedding) ei
      have ddata : d.fst.1 = d.snd.1 ∧
          (kwOrderedPortRank (kwAngularPortOrder embedding) d.fst + 1 =
              kwOrderedPortRank (kwAngularPortOrder embedding) d.snd ∨
            kwOrderedPortRank (kwAngularPortOrder embedding) d.snd + 1 =
              kwOrderedPortRank (kwAngularPortOrder embedding) d.fst) := by
        simpa only [di] using ddata'
      have edata : e.fst.1 = e.snd.1 ∧
          (kwOrderedPortRank (kwAngularPortOrder embedding) e.fst + 1 =
              kwOrderedPortRank (kwAngularPortOrder embedding) e.snd ∨
            kwOrderedPortRank (kwAngularPortOrder embedding) e.snd + 1 =
              kwOrderedPortRank (kwAngularPortOrder embedding) e.fst) := by
        simpa only [ei] using edata'
      let a := (embedding.dartAngle (kwDartOfPort G d.fst)).toReal
      let b := (embedding.dartAngle (kwDartOfPort G d.snd)).toReal
      let c := (embedding.dartAngle (kwDartOfPort G e.snd)).toReal
      have habBounds := portAngle_bounds embedding d.fst
      have hcbounds := portAngle_bounds embedding e.snd
      by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
      · have heinc : kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by
          simpa only [di, ei] using
            kwOrderedInternalDartStep_rank_lt G
              (kwAngularPortOrder embedding) hstep hinc
        have hac : a < c := by
          have had : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
              kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by
            calc
              _ < kwOrderedPortRank (kwAngularPortOrder embedding) d.snd := hinc
              _ = kwOrderedPortRank (kwAngularPortOrder embedding) e.fst :=
                congrArg (kwOrderedPortRank (kwAngularPortOrder embedding)) hconnect
              _ < _ := heinc
          exact (kwAngularPortOrder_rank_lt_iff_angle_lt embedding
            (ddata.1.trans (hconnect ▸ edata.1))).mp had
        have hdRaw : data.rawDartDirection d =
            (a + b) / 2 + Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
        have heRaw : data.rawDartDirection e =
            (b + c) / 2 + Real.pi / 2 := by
          simp only [KWAngularPortRadiusData.rawDartDirection, he, if_neg,
            heinc, if_pos]
          dsimp only [b, c]
          rw [← hconnect]
          simp
        rw [hdRaw, heRaw, kwAngleTurnPhase_coe_eq_rootRatio]
        · simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc, heinc]
          rw [← hconnect]
        · nlinarith [habBounds.1, hcbounds.2, Real.pi_pos]
        · nlinarith [habBounds.1, hcbounds.2, Real.pi_pos]
      · have hddec : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
          rcases ddata.2 with h | h <;> omega
        have hedec : kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := by
          simpa only [di, ei] using
            kwOrderedInternalDartStep_rank_gt G
              (kwAngularPortOrder embedding) hstep hddec
        have hca : c < a := by
          have had : kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
              kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
            calc
              _ < kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := hedec
              _ = kwOrderedPortRank (kwAngularPortOrder embedding) d.snd :=
                congrArg (kwOrderedPortRank (kwAngularPortOrder embedding)) hconnect.symm
              _ < _ := hddec
          exact (kwAngularPortOrder_rank_lt_iff_angle_lt embedding
            ((hconnect ▸ edata.1).symm.trans ddata.1.symm)).mp had
        have hdRaw : data.rawDartDirection d =
            (a + b) / 2 - Real.pi / 2 := by
          simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
        have heRaw : data.rawDartDirection e =
            (b + c) / 2 - Real.pi / 2 := by
          have heinc : ¬ kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
              kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by omega
          simp only [KWAngularPortRadiusData.rawDartDirection, he, if_neg,
            heinc]
          dsimp only [b, c]
          rw [← hconnect]
          simp
        rw [hdRaw, heRaw, kwAngleTurnPhase_coe_eq_rootRatio]
        · have heinc : ¬ kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
              kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by omega
          simp [KWAngularPortRadiusData.phaseGauge,
            KWAngularPortRadiusData.rawDartDirection,
            kwAngularSplitPhase, hd, he, hinc, heinc]
          rw [← hconnect]
        · nlinarith [hcbounds.1, habBounds.2, Real.pi_pos]
        · nlinarith [hcbounds.1, habBounds.2, Real.pi_pos]

end StatMech.FrontierA
