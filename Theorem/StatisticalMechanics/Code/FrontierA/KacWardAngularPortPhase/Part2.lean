/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortEmbedding.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngularPortPhase


namespace StatMech.FrontierA

open SimpleGraph

theorem KWAngularPortRadiusData.realizedDartVector_pos_raw
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    ∃ c : ℝ, 0 < c ∧
      (data.toStraightLineEmbedding.vertex d.snd -
        data.toStraightLineEmbedding.vertex d.fst) =
        (c : ℂ) * kwAngularUnit (data.rawDartDirection d) := by
  classical
  by_cases hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · obtain ⟨c, hc, hvec⟩ := kwAngularPortVertex_matching_positive
      embedding (r := (data.radius : ℝ)) hd
        (by linarith [data.edge_long (kwDartOfPort G d.fst)])
    refine ⟨c, hc, ?_⟩
    change kwAngularPortVertex embedding (data.radius : ℝ) d.snd -
        kwAngularPortVertex embedding (data.radius : ℝ) d.fst = _
    rw [hvec, embedding.dartUnit_eq_angularUnit]
    simp [KWAngularPortRadiusData.rawDartDirection, hd]
  · have dd := (kwOrderedDartPortSplitGraph_adj G
        (kwAngularPortOrder embedding) d.fst d.snd).mp d.adj |>.resolve_left hd
    let a := (embedding.dartAngle (kwDartOfPort G d.fst)).toReal
    let b := (embedding.dartAngle (kwDartOfPort G d.snd)).toReal
    have howner : d.fst.1 = d.snd.1 := dd.1
    have hvec :
        data.toStraightLineEmbedding.vertex d.snd -
            data.toStraightLineEmbedding.vertex d.fst =
          (data.radius : ℂ) *
            (kwAngularUnit b - kwAngularUnit a) := by
      change kwAngularPortVertex embedding (data.radius : ℝ) d.snd -
          kwAngularPortVertex embedding (data.radius : ℝ) d.fst = _
      unfold kwAngularPortVertex
      rw [← howner, embedding.dartUnit_eq_angularUnit,
        embedding.dartUnit_eq_angularUnit]
      dsimp only [a, b]
      ring
    by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
        kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
    · have hab : a < b :=
        (kwAngularPortOrder_rank_lt_iff_angle_lt embedding howner).mp hinc
      have hsin : 0 < Real.sin ((b - a) / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith
        · nlinarith [Real.Angle.neg_pi_lt_toReal
              (embedding.dartAngle (kwDartOfPort G d.fst)),
            Real.Angle.toReal_le_pi
              (embedding.dartAngle (kwDartOfPort G d.snd)), Real.pi_pos]
      refine ⟨2 * (data.radius : ℝ) * Real.sin ((b - a) / 2),
        mul_pos (mul_pos (by norm_num) (by exact_mod_cast data.radius_pos)) hsin, ?_⟩
      rw [hvec, kwAngularUnit_chord_of_lt hab]
      simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
      push_cast
      ring
    · have hdec : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
        rcases dd.2 with h | h <;> omega
      have hba : b < a :=
        (kwAngularPortOrder_rank_lt_iff_angle_lt embedding howner.symm).mp hdec
      have hsin : 0 < Real.sin ((a - b) / 2) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith
        · nlinarith [Real.Angle.neg_pi_lt_toReal
              (embedding.dartAngle (kwDartOfPort G d.snd)),
            Real.Angle.toReal_le_pi
              (embedding.dartAngle (kwDartOfPort G d.fst)), Real.pi_pos]
      refine ⟨2 * (data.radius : ℝ) * Real.sin ((a - b) / 2),
        mul_pos (mul_pos (by norm_num) (by exact_mod_cast data.radius_pos)) hsin, ?_⟩
      rw [hvec, kwAngularUnit_chord_of_gt hba]
      simp [KWAngularPortRadiusData.rawDartDirection, hd, hinc, a, b]
      push_cast
      ring

theorem kwAngularUnit_ne_zero (a : ℝ) : kwAngularUnit a ≠ 0 := by
  unfold kwAngularUnit
  exact Complex.exp_ne_zero _


theorem KWAngularPortRadiusData.realizedTurnPhase_eq_raw
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    data.toStraightLineEmbedding.turnPhase d e =
      kwAngleTurnPhase (data.rawDartDirection d : Real.Angle)
        (data.rawDartDirection e : Real.Angle) := by
  obtain ⟨c, hc, hd⟩ := data.realizedDartVector_pos_raw d
  obtain ⟨f, hf, he⟩ := data.realizedDartVector_pos_raw e
  rw [← data.toStraightLineEmbedding.vectorTurnPhase_eq_turnPhase d e,
    hd, he, kwVectorTurnPhase_pos_scales c f hc hf
      (kwAngularUnit (data.rawDartDirection d))
      (kwAngularUnit (data.rawDartDirection e))
      (kwAngularUnit_ne_zero _) (kwAngularUnit_ne_zero _)]
  unfold kwVectorTurnPhase kwAngularUnit
  congr 1
  · simp only [Complex.arg_exp_mul_I, Real.Angle.coe_toIocMod]
  · simp only [Complex.arg_exp_mul_I, Real.Angle.coe_toIocMod]


end StatMech.FrontierA
