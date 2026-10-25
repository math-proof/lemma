/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Def.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part6


namespace StatMech.FrontierA

theorem KWStraightLineEmbedding.cyclePolygon_edgeList
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (embedding.cyclePolygon p hp).edgeList =
      List.ofFn fun k : Fin p.darts.length ↦
        embedding.vertex (kwGraphCycleDartLoop p k).snd -
          embedding.vertex (kwGraphCycleDartLoop p k).fst := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  unfold KWFiniteSimplePolygon.edgeList
  congr 1
  funext k
  unfold KWFiniteSimplePolygon.edgeVector
  dsimp only [KWStraightLineEmbedding.cyclePolygon]
  change embedding.vertex (kwGraphCycleDartLoop p (k + 1)).fst -
      embedding.vertex (kwGraphCycleDartLoop p k).fst = _
  rw [← kwGraphCycleDartLoop_valid p hp k]


theorem KWFiniteSimplePolygon.not_collinear_three
    (polygon : KWFiniteSimplePolygon 3) :
    ¬Collinear ℝ
      ({polygon.vertex 0, polygon.vertex 1, polygon.vertex 2} : Set ℂ) := by
  intro hcol
  have h01 : polygon.vertex 0 ≠ polygon.vertex 1 :=
    polygon.vertex_injective.ne (by decide)
  have h12 : polygon.vertex 1 ≠ polygon.vertex 2 :=
    polygon.vertex_injective.ne (by decide)
  have h20 : polygon.vertex 2 ≠ polygon.vertex 0 :=
    polygon.vertex_injective.ne (by decide)
  rcases hcol.wbtw_or_wbtw_or_wbtw with hmid | hmid | hmid
  · have hstrict : Sbtw ℝ (polygon.vertex 2)
        (polygon.vertex 1) (polygon.vertex 0) :=
      ⟨hmid.symm, h12, h01.symm⟩
    exact polygon.vertex_not_strictly_between 2 1
      (by decide) (by decide) (by simpa using hstrict)
  · have hstrict : Sbtw ℝ (polygon.vertex 0)
        (polygon.vertex 2) (polygon.vertex 1) :=
      ⟨hmid.symm, h20, h12.symm⟩
    exact polygon.vertex_not_strictly_between 0 2
      (by decide) (by decide) (by simpa using hstrict)
  · have hstrict : Sbtw ℝ (polygon.vertex 1)
        (polygon.vertex 0) (polygon.vertex 2) :=
      ⟨hmid.symm, h01, h20.symm⟩
    exact polygon.vertex_not_strictly_between 1 0
      (by decide) (by decide) (by simpa using hstrict)


theorem kwVectorPhasePath_cons_congr {x : ℂ} {left right : List ℂ}
    (h : kwVectorPhasePath left = kwVectorPhasePath right)
    (hleft : left ≠ []) (hright : right ≠ [])
    (hhead : left.head hleft = right.head hright) :
    kwVectorPhasePath (x :: left) = kwVectorPhasePath (x :: right) := by
  obtain ⟨y, leftTail, rfl⟩ := List.exists_cons_of_ne_nil hleft
  obtain ⟨z, rightTail, rfl⟩ := List.exists_cons_of_ne_nil hright
  simp only [List.head_cons] at hhead
  subst z
  simp only [kwVectorPhasePath_cons_cons]
  rw [h]


theorem kwVectorTurnPhase_ear_splice
    (previous incoming outgoing next : ℂ)
    (hp : previous ≠ 0) (hi : incoming ≠ 0)
    (ho : outgoing ≠ 0) (hn : next ≠ 0)
    (hmiddle : kwComplexCross incoming outgoing ≠ 0)
    (hrightTurn :
      (Complex.arg next : Real.Angle) -
        (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
    (hleft :
      (0 < kwComplexCross previous incoming ∧
          0 < kwComplexCross previous (incoming + outgoing)) ∨
        (kwComplexCross previous incoming < 0 ∧
          kwComplexCross previous (incoming + outgoing) < 0))
    (hright :
      (0 < kwComplexCross (incoming + outgoing) outgoing ∧
          0 < kwComplexCross (incoming + outgoing) next) ∨
        (kwComplexCross (incoming + outgoing) outgoing < 0 ∧
          kwComplexCross (incoming + outgoing) next < 0)) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next := by
  exact kwAngleTurnPhase_ear_splice_vectors previous incoming outgoing next
    hp hi ho hn hmiddle hrightTurn hleft hright


theorem kwVectorTurnPhase_straight_splice
    (previous incoming outgoing next : ℂ)
    (houtgoing :
      (Complex.arg outgoing : Real.Angle) =
        (Complex.arg incoming : Real.Angle))
    (hdiagonal :
      (Complex.arg (incoming + outgoing) : Real.Angle) =
        (Complex.arg incoming : Real.Angle)) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next := by
  simp only [kwVectorTurnPhase, houtgoing, hdiagonal]
  simp [kwAngleTurnPhase]


theorem kwVectorTurnPhase_straight_splice_of_sameRay
    (previous incoming outgoing next : ℂ)
    (hi : incoming ≠ 0) (ho : outgoing ≠ 0)
    (hsame : SameRay ℝ incoming outgoing) :
    kwVectorTurnPhase previous incoming *
          kwVectorTurnPhase incoming outgoing *
          kwVectorTurnPhase outgoing next =
      kwVectorTurnPhase previous (incoming + outgoing) *
        kwVectorTurnPhase (incoming + outgoing) next := by
  have houtgoing : outgoing.arg = incoming.arg := by
    rcases Complex.sameRay_iff.mp hsame with hzero | hzero | harg
    · exact (hi hzero).elim
    · exact (ho hzero).elim
    · exact harg.symm
  have hsum : incoming + outgoing ≠ 0 := by
    intro hzero
    have hnorm := hsame.norm_add
    rw [hzero, norm_zero] at hnorm
    have hiNorm : 0 < ‖incoming‖ := norm_pos_iff.mpr hi
    have hoNorm : 0 < ‖outgoing‖ := norm_pos_iff.mpr ho
    nlinarith
  have hsumRay : SameRay ℝ (incoming + outgoing) incoming :=
    SameRay.rfl.add_left hsame.symm
  have hdiagonal : (incoming + outgoing).arg = incoming.arg := by
    rcases Complex.sameRay_iff.mp hsumRay with hzero | hzero | harg
    · exact (hsum hzero).elim
    · exact (hi hzero).elim
    · exact harg
  exact kwVectorTurnPhase_straight_splice previous incoming outgoing next
    (congrArg (fun r : ℝ ↦ (r : Real.Angle)) houtgoing)
    (congrArg (fun r : ℝ ↦ (r : Real.Angle)) hdiagonal)


theorem KWFiniteSimplePolygon.straight_local_phase
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n)
    (hbetween : Wbtw ℝ (polygon.vertex i)
      (polygon.vertex (i + 1)) (polygon.vertex (i + 2))) :
    kwVectorTurnPhase (polygon.edgeVector (i - 1))
          (polygon.edgeVector i) *
        kwVectorTurnPhase (polygon.edgeVector i)
          (polygon.edgeVector (i + 1)) *
        kwVectorTurnPhase (polygon.edgeVector (i + 1))
          (polygon.edgeVector (i + 2)) =
      kwVectorTurnPhase (polygon.edgeVector (i - 1))
          (polygon.edgeVector i + polygon.edgeVector (i + 1)) *
        kwVectorTurnPhase
          (polygon.edgeVector i + polygon.edgeVector (i + 1))
          (polygon.edgeVector (i + 2)) := by
  apply kwVectorTurnPhase_straight_splice_of_sameRay
  · exact polygon.edgeVector_ne_zero i
  · exact polygon.edgeVector_ne_zero (i + 1)
  · unfold KWFiniteSimplePolygon.edgeVector
    have hidx : i + 1 + 1 = i + 2 := by
      rw [add_assoc]
      congr 1
      apply Fin.ext
      have hthree := polygon.three_le
      have hn : 2 < n := by omega
      simp [Fin.val_add, Nat.mod_eq_of_lt hn]
    rw [hidx]
    exact hbetween.sameRay_vsub


theorem KWFiniteSimplePolygon.collinear_local_phase
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (i : Fin n)
    (hcol : Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    kwVectorTurnPhase (polygon.edgeVector (i - 1))
          (polygon.edgeVector i) *
        kwVectorTurnPhase (polygon.edgeVector i)
          (polygon.edgeVector (i + 1)) *
        kwVectorTurnPhase (polygon.edgeVector (i + 1))
          (polygon.edgeVector (i + 2)) =
      kwVectorTurnPhase (polygon.edgeVector (i - 1))
          (polygon.edgeVector i + polygon.edgeVector (i + 1)) *
        kwVectorTurnPhase
          (polygon.edgeVector i + polygon.edgeVector (i + 1))
          (polygon.edgeVector (i + 2)) :=
  polygon.straight_local_phase i
    (polygon.consecutive_wbtw_of_collinear i hcol)


end StatMech.FrontierA
