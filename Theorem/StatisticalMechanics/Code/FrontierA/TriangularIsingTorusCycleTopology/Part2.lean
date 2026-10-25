/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
open scoped BigOperators


namespace StatMech.FrontierA

theorem triangularIntVector_arg (a : Fin 6) :
    (Complex.arg (triangularIntVector a) : Real.Angle) =
      triangularTorusDirectionAngle a := by
  fin_cases a
  · simp [triangularIntVector, triangularIntPoint, triangularIntStep,
      triangularTorusDirectionAngle, triangularTorusDirectionAngleReal,
      Complex.arg_neg_one]
  · simp [triangularIntVector, triangularIntPoint, triangularIntStep,
      triangularTorusDirectionAngle, triangularTorusDirectionAngleReal,
      Complex.arg_one]
  · simp [triangularIntVector, triangularIntPoint, triangularIntStep,
      triangularTorusDirectionAngle, triangularTorusDirectionAngleReal,
      Complex.arg_neg_I]
    rw [<- Real.Angle.coe_neg]
    congr 1
    ring
  · simp [triangularIntVector, triangularIntPoint, triangularIntStep,
      triangularTorusDirectionAngle, triangularTorusDirectionAngleReal,
      Complex.arg_I]
  · dsimp [triangularIntVector, triangularIntPoint,
      triangularIntStep, triangularTorusDirectionAngle,
      triangularTorusDirectionAngleReal]
    norm_num
    rw [show (-1 : Complex) + -Complex.I =
      -((1 : Complex) + Complex.I) by ring]
    rw [Complex.arg_neg_coe_angle (by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre),
      complex_arg_one_add_I_angle]
    have hang : ((Real.pi / 4 : Real) : Real.Angle) + Real.pi =
        ((-3 * Real.pi / 4 : Real) : Real.Angle) := by
      rw [<- Real.Angle.coe_add]
      rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
      exact ⟨1, by push_cast; ring⟩
    rw [hang]
    congr 1
    ring
  · simpa [triangularIntVector, triangularIntPoint, triangularIntStep,
      triangularTorusDirectionAngle, triangularTorusDirectionAngleReal] using
      complex_arg_one_add_I_angle

theorem triangularIntPoint_add_sub (p q : Int × Int) :
    triangularIntPoint (p + q) - triangularIntPoint p =
      triangularIntPoint q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp [triangularIntPoint]
  push_cast
  ring

theorem triangularIntSimplePolygon_edgeVector
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (hn : 3 <= n) (hinjective : Function.Injective (triangularIntPos direction))
    (i : Fin n) :
    (triangularIntSimplePolygon direction hclosed hn hinjective).edgeVector i =
      triangularIntVector (direction i) := by
  unfold KWFiniteSimplePolygon.edgeVector
  dsimp only [triangularIntSimplePolygon]
  rw [triangularIntPos_succ direction hclosed i]
  exact triangularIntPoint_add_sub _ _

theorem kwVectorTurnPhase_triangularIntVector
    (a b : Fin 6) :
    kwVectorTurnPhase (triangularIntVector a) (triangularIntVector b) =
      kwAngleTurnPhase (triangularTorusDirectionAngle a)
        (triangularTorusDirectionAngle b) := by
  unfold kwVectorTurnPhase
  rw [triangularIntVector_arg, triangularIntVector_arg]


theorem exists_triangularTorusTurnExponent_sum_eq_eight_mul_odd_of_closed
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hnonbacktracking : forall k,
      direction (k + 1) ≠ triangularTorusDirectionReverse (direction k))
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (hn : 3 <= n)
    (hinjective : Function.Injective (triangularIntPos direction)) :
    exists m : Int,
      (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) = 8 * (2 * m + 1) := by
  let polygon := triangularIntSimplePolygon direction hclosed hn hinjective
  have hpolygon := kwFiniteSimplePolygonPhaseSign_adaptive polygon
  have hphase : kwLoopPhaseProduct
      (fun a b => kwAngleTurnPhase
        (triangularTorusDirectionAngle a)
        (triangularTorusDirectionAngle b)) direction = -1 := by
    have hedges : polygon.edgeList =
        List.ofFn (fun i => triangularIntVector (direction i)) := by
      unfold KWFiniteSimplePolygon.edgeList
      congr 1
      funext i
      dsimp only [polygon]
      exact triangularIntSimplePolygon_edgeVector
        direction hclosed hn hinjective i
    rw [hedges, kwVectorPhaseCycle_ofFn] at hpolygon
    unfold kwLoopPhaseProduct at hpolygon ⊢
    simpa only [kwVectorTurnPhase_triangularIntVector] using hpolygon
  obtain ⟨winding, hturn⟩ :=
    kw_totalPrincipalTurn_eq_int_mul_two_pi
      triangularTorusDirectionAngle direction
  have hodd : Odd winding :=
    kw_odd_winding_of_angleTurnPhase_eq_neg_one
      triangularTorusDirectionAngle direction winding hturn hphase
  have hsum :
      (∑ k, (triangularTorusDirectionAngle (direction (k + 1)) -
        triangularTorusDirectionAngle (direction k)).toReal : Real) =
      ((∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1)) : Int) : Real) *
          (Real.pi / 4) := by
    rw [show (∑ k, (triangularTorusDirectionAngle (direction (k + 1)) -
        triangularTorusDirectionAngle (direction k)).toReal : Real) =
        ∑ k, (triangularTorusTurnExponent
          (direction k) (direction (k + 1)) : Real) *
            (Real.pi / 4) by
      apply Finset.sum_congr rfl
      intro k _
      exact triangularTorusDirectionAngle_turn _ _ (hnonbacktracking k)]
    rw [<- Finset.sum_mul]
    norm_cast
  have hreal :
      (((∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1)) : Int) : Real) *
          (Real.pi / 4)) =
        (winding : Real) * (2 * Real.pi) := hsum.symm.trans hturn
  have hcast :
      (((∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1)) : Int) : Real)) =
        8 * (winding : Real) := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp at hreal ⊢
    nlinarith
  have hint :
      (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) = 8 * winding := by
    exact_mod_cast hcast
  obtain ⟨m, hm⟩ := hodd
  refine ⟨m, ?_⟩
  rw [hint, hm]

end StatMech.FrontierA
