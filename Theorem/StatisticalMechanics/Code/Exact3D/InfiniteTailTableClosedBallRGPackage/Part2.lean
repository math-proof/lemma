/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailTableWitnessPackage.Part11
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBallRG.Part5
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage.Part2


namespace StatMech

namespace Exact3D

namespace InfiniteTailTableClosedBallRGPackage

variable {ι Case Coord : Type*} {TailIndex : Type}

variable [DecidableEq Case] [DecidableEq Coord]

variable {M : CriticalModel ι} {n : ℕ}


@[simp] theorem tableCertifiedTotalBound_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tableCertifiedTotalBound =
      P.tableWitness.tableCertifiedTotalBound :=
  rfl

@[simp] theorem tableFiniteBudget_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tableFiniteBudget = P.tableWitness.tableFiniteBudget :=
  rfl

@[simp] theorem tablePrefixBudget_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tablePrefixBudget = P.tableWitness.tablePrefixBudget :=
  rfl

@[simp] theorem tailTotalTsum_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum = P.tableWitness.tailTotalTsum :=
  rfl

@[simp] theorem tailBudget_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailBudget = P.tableWitness.tailBudget :=
  rfl

@[simp] theorem tailContribution_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailContribution = P.tableWitness.tailContribution :=
  rfl

@[simp] theorem closedBallResidual_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallResidual = P.closedBallRG.closedBall.residual :=
  rfl

@[simp] theorem closedBallRadius_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallRadius = P.closedBallRG.closedBall.radius :=
  rfl

@[simp] theorem closedBallCenter_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallCenter = P.closedBallRG.closedBall.center :=
  rfl

@[simp] theorem closedBallContraction_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallContraction = P.closedBallRG.closedBall.contraction :=
  rfl

@[simp] theorem closedBallFixedPoint_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallFixedPoint = P.closedBallRG.closedBall.fixedPoint :=
  rfl


theorem closedBallRadius_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ P.closedBallRadius := by
  simpa [closedBallRadius] using
    P.closedBallRG.closedBall.radius_nonneg


theorem closedBallResidual_bound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    (P.closedBallContraction.map P.closedBallCenter).dist
        P.closedBallCenter ≤
      P.closedBallResidual := by
  simpa [closedBallContraction, closedBallCenter, closedBallResidual] using
    P.closedBallRG.closedBall.residual_bound


theorem closedBallRadius_bound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallResidual +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  simpa [closedBallResidual, closedBallContraction, closedBallRadius] using
    P.closedBallRG.closedBall.radius_bound


theorem mapsClosedBall
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailState.MapsClosedBall
      P.closedBallContraction.map
      P.closedBallCenter P.closedBallRadius := by
  simpa [closedBallContraction, closedBallCenter, closedBallRadius] using
    P.closedBallRG.closedBall.mapsClosedBall


theorem closedBallFixedPoint_mem_closedBall
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailState.ClosedBall
      P.closedBallCenter P.closedBallRadius
      P.closedBallFixedPoint := by
  simpa [closedBallCenter, closedBallRadius, closedBallFixedPoint] using
    P.closedBallRG.closedBall.fixedPoint_mem


theorem fixedPoint_mem_closedBall
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    FinitePlusTailState.ClosedBall
      P.closedBallCenter P.closedBallRadius
      P.closedBallRG.closedBall.fixedPoint := by
  simpa [closedBallFixedPoint] using P.closedBallFixedPoint_mem_closedBall


theorem closedBallFixedPoint_isFixed
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallContraction.map P.closedBallFixedPoint =
      P.closedBallFixedPoint := by
  simpa [closedBallContraction, closedBallFixedPoint] using
    P.closedBallRG.closedBall.fixedPoint_isFixed


theorem closedBall_fixedPoint_isFixed
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.closedBallContraction.map P.closedBallRG.closedBall.fixedPoint =
      P.closedBallRG.closedBall.fixedPoint := by
  simpa [closedBallFixedPoint] using P.closedBallFixedPoint_isFixed


theorem tableCertifiedTotalBound_le_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tableCertifiedTotalBound ≤ P.closedBallResidual :=
  P.tableBudget_le_residual

@[simp] theorem tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tableCertifiedTotalBound = P.tablePrefixBudget + P.tailBudget :=
  rfl


theorem tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {prefixBound tailBound' : ℝ}
    (hprefix : P.tablePrefixBudget ≤ prefixBound)
    (htail : P.tailBudget ≤ tailBound') :
    P.tableCertifiedTotalBound ≤ prefixBound + tailBound' := by
  simpa [P.tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget] using
    add_le_add hprefix htail


theorem tailTotalTsum_le_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum ≤ P.tableCertifiedTotalBound :=
  P.tableWitness.tailTotalTsum_le_tableCertifiedTotalBound


theorem tailTotalTsum_le_tablePrefixBudget_add_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum ≤ P.tablePrefixBudget + P.tailBudget := by
  simpa [P.tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget] using
    P.tailTotalTsum_le_tableCertifiedTotalBound


theorem tailTotalTsum_le_of_tableCertifiedTotalBound_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {B : ℝ} (hB : P.tableCertifiedTotalBound ≤ B) :
    P.tailTotalTsum ≤ B :=
  le_trans P.tailTotalTsum_le_tableCertifiedTotalBound hB


theorem tailTotalTsum_le_of_tablePrefixBudget_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {prefixBound tailBound' : ℝ}
    (hprefix : P.tablePrefixBudget ≤ prefixBound)
    (htail : P.tailBudget ≤ tailBound') :
    P.tailTotalTsum ≤ prefixBound + tailBound' :=
  P.tailTotalTsum_le_of_tableCertifiedTotalBound_le
    (P.tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBudget
      hprefix htail)


theorem summable_tailContribution
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    Summable P.tailContribution := by
  simpa [tailContribution] using P.tableWitness.summable_tailContribution


theorem tailTotalTsum_eq_tsum
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum = ∑' a, P.tailContribution a := by
  simpa [tailTotalTsum, tailContribution] using
    P.tableWitness.tailTotalTsum_eq_tsum


theorem tail_tsum_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ ∑' a, P.tailContribution a := by
  simpa [tailContribution] using P.tableWitness.tail_tsum_nonneg


theorem tail_tsum_le_tableCertifiedTotalBound
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    (∑' a, P.tailContribution a) ≤ P.tableCertifiedTotalBound := by
  simpa [tailContribution, tableCertifiedTotalBound] using
    P.tableWitness.tail_tsum_le_tableCertifiedTotalBound


theorem tail_tsum_le_of_tableCertifiedTotalBound_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {B : ℝ} (hB : P.tableCertifiedTotalBound ≤ B) :
    (∑' a, P.tailContribution a) ≤ B :=
  le_trans P.tail_tsum_le_tableCertifiedTotalBound hB


theorem tail_tsum_le_of_tablePrefixBudget_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {prefixBound tailBound' : ℝ}
    (hprefix : P.tablePrefixBudget ≤ prefixBound)
    (htail : P.tailBudget ≤ tailBound') :
    (∑' a, P.tailContribution a) ≤ prefixBound + tailBound' :=
  P.tail_tsum_le_of_tableCertifiedTotalBound_le
    (P.tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBudget
      hprefix htail)


theorem tail_tsum_le_tablePrefixBudget_add_tailBudget
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    (∑' a, P.tailContribution a) ≤ P.tablePrefixBudget + P.tailBudget := by
  simpa [P.tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget] using
    P.tail_tsum_le_tableCertifiedTotalBound


theorem tailContribution_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (a : Coord) :
    0 ≤ P.tailContribution a :=
  P.tableWitness.tailContribution_nonneg a


theorem tailTotalTsum_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ P.tailTotalTsum :=
  P.tableWitness.tailTotalTsum_nonneg


theorem tableCertifiedTotalBound_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ P.tableCertifiedTotalBound :=
  le_trans P.tailTotalTsum_nonneg
    P.tailTotalTsum_le_tableCertifiedTotalBound


theorem tailBudget_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ P.tailBudget :=
  P.tableWitness.tailBudget_nonneg


theorem closedBallResidual_nonneg
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    0 ≤ P.closedBallResidual :=
  le_trans P.tableCertifiedTotalBound_nonneg
    P.tableCertifiedTotalBound_le_closedBallResidual


theorem tailTotalTsum_le_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum ≤ P.closedBallResidual :=
  le_trans P.tableWitness.tailTotalTsum_le_tableCertifiedTotalBound
    P.tableBudget_le_residual


theorem tail_tsum_le_closedBallResidual
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    (∑' a, P.tailContribution a) ≤ P.closedBallResidual :=
  le_trans P.tail_tsum_le_tableCertifiedTotalBound
    P.tableCertifiedTotalBound_le_closedBallResidual


theorem tailTotalTsum_le_of_closedBallResidual_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {B : ℝ} (hB : P.closedBallResidual ≤ B) :
    P.tailTotalTsum ≤ B :=
  le_trans P.tailTotalTsum_le_closedBallResidual hB


theorem tail_tsum_le_of_closedBallResidual_le
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    {B : ℝ} (hB : P.closedBallResidual ≤ B) :
    (∑' a, P.tailContribution a) ≤ B :=
  le_trans P.tail_tsum_le_closedBallResidual hB

@[simp] theorem certificate_thermalEigenvalue_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).thermalEigenvalue = P.closedBallRG.thermal :=
  rfl

@[simp] theorem certificate_scale_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).scale = scale :=
  rfl


@[simp] theorem certificate_fixedPoint_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).fixedPointData.fixedPoint =
      P.closedBallRG.closedBall.fixedPoint :=
  rfl


@[simp] theorem certificate_R_map_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).R.map =
      P.closedBallContraction.map :=
  rfl


theorem certificate_predictedExponent_eq
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).predictedExponent =
      predictedNu scale P.closedBallRG.thermal :=
  rfl


theorem certificate_fixedPointEnclosure
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).FixedPointEnclosure :=
  P.closedBallRG.certificate_fixedPointEnclosure scale M


theorem certificate_finiteCaseChecks
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).FiniteCaseChecks :=
  P.closedBallRG.certificate_finiteCaseChecks scale M


theorem certificate_tailBounds
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).TailBounds :=
  P.closedBallRG.certificate_tailBounds scale M


theorem certificate_linearizationEnclosure
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).LinearizationEnclosure :=
  P.closedBallRG.certificate_linearizationEnclosure scale M


theorem certificate_hyperbolicSplitting
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).HyperbolicSplitting :=
  P.closedBallRG.certificate_hyperbolicSplitting scale M


theorem certificate_orbitEntry
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    (P.certificate scale).OrbitEntry :=
  P.closedBallRG.certificate_orbitEntry scale M


theorem certificate_fixedPoint_mem_closedBall
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) :
    FinitePlusTailState.ClosedBall
      P.closedBallCenter P.closedBallRadius
      (P.certificate scale).fixedPointData.fixedPoint :=
  P.closedBallRG.certificate_fixedPoint_mem_closedBall scale M


theorem certificate_iterate_mem_closedBall
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale)
    {x : (P.certificate scale).H.carrier}
    (hx :
      FinitePlusTailState.ClosedBall
        P.closedBallCenter P.closedBallRadius x)
    (k : ℕ) :
    FinitePlusTailState.ClosedBall
      P.closedBallCenter P.closedBallRadius
      ((((P.certificate scale).R.map)^[k]) x) :=
  P.closedBallRG.certificate_iterate_mem_closedBall scale M hx k


theorem tableCertifiedTotalBound_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tableCertifiedTotalBound +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  calc
    P.tableCertifiedTotalBound +
        P.closedBallContraction.c * P.closedBallRadius ≤
        P.closedBallResidual +
          P.closedBallContraction.c * P.closedBallRadius := by
      exact add_le_add P.tableCertifiedTotalBound_le_closedBallResidual
        (le_refl (P.closedBallContraction.c * P.closedBallRadius))
    _ ≤ P.closedBallRadius := by
      simpa [closedBallResidual, closedBallRadius, closedBallContraction] using
        P.closedBallRG.closedBall.radius_bound


theorem tailTotalTsum_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    P.tailTotalTsum +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  calc
    P.tailTotalTsum +
        P.closedBallContraction.c * P.closedBallRadius ≤
        P.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius := by
      exact add_le_add P.tailTotalTsum_le_tableCertifiedTotalBound
        (le_refl (P.closedBallContraction.c * P.closedBallRadius))
    _ ≤ P.closedBallRadius :=
      P.tableCertifiedTotalBound_plus_mul_radius_le_radius


theorem tail_tsum_plus_mul_radius_le_radius
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
    (∑' a, P.tailContribution a) +
        P.closedBallContraction.c * P.closedBallRadius ≤
      P.closedBallRadius := by
  calc
    (∑' a, P.tailContribution a) +
        P.closedBallContraction.c * P.closedBallRadius ≤
        P.tableCertifiedTotalBound +
          P.closedBallContraction.c * P.closedBallRadius := by
      exact add_le_add P.tail_tsum_le_tableCertifiedTotalBound
        (le_refl (P.closedBallContraction.c * P.closedBallRadius))
    _ ≤ P.closedBallRadius :=
      P.tableCertifiedTotalBound_plus_mul_radius_le_radius


theorem certificate_valid_of_bridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    (P.certificate scale).Valid correlationLength :=
  P.closedBallRG.certificate_valid_of_bridge
    scale M correlationLength hbridge


theorem certificate_rgToExponentBridge_of_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    (hν : HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  P.closedBallRG.certificate_rgToExponentBridge_of_hasCriticalNu
    scale M correlationLength hν


theorem certificate_valid_of_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    (hν : HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_hasCriticalNu
      scale correlationLength hν)


theorem certificate_hasCriticalNu_of_hasCriticalNu
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) {correlationLength : ℝ → ℝ}
    (hν : HasCriticalNu M correlationLength
      (P.certificate scale).predictedExponent) :
    HasCriticalNu M correlationLength (P.certificate scale).predictedExponent :=
  hν


theorem certificate_hasCriticalNu_of_bridge
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) (correlationLength : ℝ → ℝ)
    (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_bridge
    scale correlationLength hbridge).hasCriticalNu


theorem certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (P.certificate scale).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred


theorem certificate_valid_of_bridge_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (P.certificate scale).Valid correlationLength :=
  P.certificate_valid_of_bridge scale correlationLength
    (P.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
      scale hpred hbridge)


theorem certificate_hasCriticalNu_of_bridge_congr_predictedExponent
    (P : InfiniteTailTableClosedBallRGPackage
      (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
    (scale : BlockScale) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength (P.certificate scale).predictedExponent :=
  (P.certificate_valid_of_bridge_congr_predictedExponent
    scale hpred hbridge).hasCriticalNu


end InfiniteTailTableClosedBallRGPackage
end Exact3D
end StatMech
