/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Def.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part4
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


theorem abigMag_nonneg (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V)
    (beta h : Real) : 0 <= abigMag G J o beta h :=
  measureReal_nonneg


theorem abigParam_eq_zero_beta_of_nonpos (J : Sym2 V -> Real) (beta h : Real)
    (hbeta : beta <= 0) (hJ : forall e, 0 <= J e) :
    abigParam J beta h = abigParam J 0 h := by
  funext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · rfl
      · rfl
      · rfl
      · have hp : pBeta (J s(x, y)) beta <= 0 := by
          unfold pBeta
          have hexp : 1 <= Real.exp (-beta * J s(x, y)) := by
            rw [Real.one_le_exp_iff]
            exact mul_nonneg (neg_nonneg.mpr hbeta) (hJ s(x, y))
          linarith
        simp [abigParam_some_some, Real.toNNReal_eq_zero.mpr hp, pBeta]
        exact mul_nonpos_of_nonpos_of_nonneg hbeta (hJ s(x, y))

theorem abigMag_eq_zero_beta_of_nonpos (G : SimpleGraph V)
    (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hbeta : beta <= 0) (hJ : forall e, 0 <= J e) :
    abigMag G J o beta h = abigMag G J o 0 h := by
  have hm : abigMeasure J beta h = abigMeasure J 0 h := by
    unfold abigMeasure
    congr 1
    exact abigParam_eq_zero_beta_of_nonpos J beta h hbeta hJ
  unfold abigMag
  rw [hm]


theorem abigMag_eq_max_beta_zero (G : SimpleGraph V)
    (J : Sym2 V -> Real) (o : V) (beta h : Real) (hJ : forall e, 0 <= J e) :
    abigMag G J o beta h = abigMag G J o (max beta 0) h := by
  by_cases hbeta : 0 <= beta
  · rw [max_eq_left hbeta]
  · rw [max_eq_right (le_of_not_ge hbeta)]
    exact abigMag_eq_zero_beta_of_nonpos G J o beta h (le_of_not_ge hbeta) hJ


end Sharpness
end StatMech
