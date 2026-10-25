/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Def.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part3
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem ons_reciprocalInterpolationCoeff_zero (q : Complex) :
    ons_reciprocalInterpolationCoeff q (0 : Fin 3) =
      q ^ 2 - (q ^ 2)⁻¹ := by
  simp [ons_reciprocalInterpolationCoeff]

@[simp] theorem ons_reciprocalInterpolationCoeff_one (q : Complex) :
    ons_reciprocalInterpolationCoeff q (1 : Fin 3) =
      ((q ^ 2)⁻¹ + 1) / 2 := by
  simp [ons_reciprocalInterpolationCoeff]

@[simp] theorem ons_reciprocalInterpolationCoeff_two (q : Complex) :
    ons_reciprocalInterpolationCoeff q (2 : Fin 3) =
      ((q ^ 2)⁻¹ - 1) / 2 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp [ons_reciprocalInterpolationCoeff, h20, h21]

@[simp] theorem ons_reciprocalInterpolationValue_zero (q : Complex) :
    ons_reciprocalInterpolationValue q (0 : Fin 3) = 0 := by
  simp [ons_reciprocalInterpolationValue]

@[simp] theorem ons_reciprocalInterpolationValue_one (q : Complex) :
    ons_reciprocalInterpolationValue q (1 : Fin 3) = q := by
  simp [ons_reciprocalInterpolationValue]

@[simp] theorem ons_reciprocalInterpolationValue_two (q : Complex) :
    ons_reciprocalInterpolationValue q (2 : Fin 3) = -q := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp [ons_reciprocalInterpolationValue, h20, h21]

theorem sum_reciprocalInterpolationCoeff (q : Complex) (hq : q ≠ 0) :
    ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s = q ^ 2 := by
  rw [Fin.sum_univ_three]
  simp only [ons_reciprocalInterpolationCoeff_zero,
    ons_reciprocalInterpolationCoeff_one,
    ons_reciprocalInterpolationCoeff_two]
  field_simp
  ring

theorem sum_reciprocalInterpolationCoeff_mul_value
    (q : Complex) (hq : q ≠ 0) :
    ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
      ons_reciprocalInterpolationValue q s = q := by
  rw [Fin.sum_univ_three]
  simp only [ons_reciprocalInterpolationCoeff_zero,
    ons_reciprocalInterpolationCoeff_one,
    ons_reciprocalInterpolationCoeff_two,
    ons_reciprocalInterpolationValue_zero,
    ons_reciprocalInterpolationValue_one,
    ons_reciprocalInterpolationValue_two]
  field_simp
  ring

theorem sum_reciprocalInterpolationCoeff_mul_value_sq
    (q : Complex) (hq : q ≠ 0) :
    ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
      ons_reciprocalInterpolationValue q s ^ 2 = 1 := by
  rw [Fin.sum_univ_three]
  simp only [ons_reciprocalInterpolationCoeff_zero,
    ons_reciprocalInterpolationCoeff_one,
    ons_reciprocalInterpolationCoeff_two,
    ons_reciprocalInterpolationValue_zero,
    ons_reciprocalInterpolationValue_one,
    ons_reciprocalInterpolationValue_two]
  field_simp
  ring


theorem reciprocalInterpolation_affine_sq
    (A B q : Complex) (hq : q ≠ 0) :
    q ^ 2 * (A + q⁻¹ * B) ^ 2 =
      ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
        (A + ons_reciprocalInterpolationValue q s * B) ^ 2 := by
  rw [Fin.sum_univ_three]
  simp only [ons_reciprocalInterpolationCoeff_zero,
    ons_reciprocalInterpolationCoeff_one,
    ons_reciprocalInterpolationCoeff_two,
    ons_reciprocalInterpolationValue_zero,
    ons_reciprocalInterpolationValue_one,
    ons_reciprocalInterpolationValue_two]
  field_simp
  ring


theorem reciprocalKWDet_eq_bounded_three_point
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (edge : Sym2 V)
    (q : Complex) (hq : q ≠ 0) :
    q ^ 2 *
        (1 - kwGraphTransition G
          (ons_setGraphEdgeWeight weight edge q⁻¹)
          embedding.turnPhase).det =
      ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
        (1 - kwGraphTransition G
          (ons_setGraphEdgeWeight weight edge
            (ons_reciprocalInterpolationValue q s))
          embedding.turnPhase).det := by
  simp_rw [kacWard_straightLine_arbitrary_adaptive G embedding]
  let A := kwEvenPolynomial G (ons_setGraphEdgeWeight weight edge 0)
  let B := ons_kwEvenEdgeCoefficient G weight edge
  have haff (z : Complex) :
      kwEvenPolynomial G (ons_setGraphEdgeWeight weight edge z) = A + z * B :=
    kwEvenPolynomial_setEdge_affine G weight edge z
  simp_rw [haff]
  exact reciprocalInterpolation_affine_sq A B q hq


end
end StatMech.Onsager
