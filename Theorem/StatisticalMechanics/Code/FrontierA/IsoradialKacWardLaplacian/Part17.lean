/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part18


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


theorem sum_cycleSelections_eq_prod_one_sub
    {C : Type*} [Fintype C]
    (holonomy : C -> Complex) :
    (∑ selected : Finset C,
        (-1 : Complex) ^ selected.card *
          ∏ c ∈ selected, holonomy c) =
      ∏ c : C, (1 - holonomy c) := by
  classical
  have h := Fintype.prod_add
    (fun c : C => -holonomy c) (fun _c : C => (1 : Complex))
  symm
  simpa [prod_neg, sub_eq_add_neg, add_comm, mul_comm] using h


theorem pairedBoundaryCharacter_eq_formanCycleCoefficient
    (holonomy : Complex) (hholonomy : holonomy ≠ 0) :
    (1 - holonomy) * (1 - holonomy⁻¹) =
      formanCycleCoefficient holonomy := by
  unfold formanCycleCoefficient
  rw [mul_sub, mul_one]
  have hinv : holonomy * holonomy⁻¹ = 1 :=
    mul_inv_cancel₀ hholonomy
  rw [sub_mul, one_mul, hinv]
  ring


theorem prod_pairedBoundaryCharacter_eq_formanCRSFCoefficient
    {C : Type*} [Fintype C]
    (holonomy : C -> Complex) (hholonomy : forall c, holonomy c ≠ 0) :
    (∏ c : C, (1 - holonomy c) * (1 - (holonomy c)⁻¹)) =
      formanCRSFCoefficient holonomy := by
  unfold formanCRSFCoefficient
  apply Finset.prod_congr rfl
  intro c _
  exact pairedBoundaryCharacter_eq_formanCycleCoefficient
    (holonomy c) (hholonomy c)

omit [DecidableEq E] in


theorem criticalKacWard_det_eq_laplacian_of_subgraphFactorization
    (kacWard : Matrix D D Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (hsubgraphFactorization :
      (1 - kacWard).det =
        (((-1 : Complex) ^ Fintype.card V *
            kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
            (∏ v : V, coneQuarterPhase exceptional v) *
            kwLaplacianEdgePrefactor thetaEdge) *
          (finiteTwistedLaplacian
            (isoradialMuConductance thetaVertex) transport).det)) :
    (1 - kacWard).det =
      (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det := by
  rw [hsubgraphFactorization,
    det_finiteTwistedLaplacian_isoradialMu]
  calc
    ((-1 : Complex) ^ Fintype.card V *
          kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
          (∏ v : V, coneQuarterPhase exceptional v) *
          kwLaplacianEdgePrefactor thetaEdge) *
        (Complex.I ^ Fintype.card V *
          (finiteTwistedLaplacian
            (isoradialLaplacianConductance thetaVertex) transport).det) =
      (((-1 : Complex) ^ Fintype.card V *
          (∏ v : V, coneQuarterPhase exceptional v) *
          Complex.I ^ Fintype.card V) *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det) := by
      ring
    _ = (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det := by
      rw [conePhase_prefactor_eq_exceptionSign]

end StatMech.FrontierA
