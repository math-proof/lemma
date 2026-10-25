/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part5
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
import Def.StatisticalMechanics.Code.FK.HexagonalSharpnessOffCentre.Part4
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.RevealmentTranslation

theorem hexagonalSharpConstant_pos (beta0 : Real) :
    0 < hexagonalSharpConstant beta0 := by
  unfold hexagonalSharpConstant
  positivity

theorem hexagonal_outer_inner_differential_uniform
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    hexagonalSharpConstant beta0 *
        (((n : Real) / hexagonalOuterInnerSig n q beta) *
          hexagonalOuterInnerTheta q beta n) ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  have hbeta0nonneg : 0 ≤ beta0 := hbeta.le.trans hbeta0
  have hkappa := exp_neg_pow_six_le_hexagonalInnerKappa
    n hn beta0 hbeta0nonneg
  have hmain := hexagonal_outer_inner_differential_linear
    n hn q beta beta0 hq hbeta hbeta0
  have htheta0 := hexagonalOuterInnerTheta_nonneg q beta hq hbeta n
  have hsig := hexagonalOuterInnerSig_pos n hn q beta hq hbeta
  have hnR : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    hexagonalSharpConstant beta0 *
        (((n : Real) / hexagonalOuterInnerSig n q beta) *
          hexagonalOuterInnerTheta q beta n) ≤
      (hexagonalInnerKappa n beta0 / 8) *
        (((n : Real) / hexagonalOuterInnerSig n q beta) *
          hexagonalOuterInnerTheta q beta n) := by
        apply mul_le_mul_of_nonneg_right
        · exact div_le_div_of_nonneg_right hkappa (by norm_num)
        · positivity
    _ = hexagonalInnerKappa n beta0 *
        (hexagonalOuterInnerTheta q beta n /
          (8 * hexagonalOuterInnerSig n q beta / (n : Real))) := by
      field_simp
    _ ≤ hexagonalOuterInnerThetaPrime n q beta := hmain

end StatMech.FK.PeriodicPlanar
