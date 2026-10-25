/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


theorem kwGraphFormalLogCoeff_eq_tsum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (m : Sym2 V →₀ ℕ) :
    kwGraphFormalLogCoeff G phase m =
      -(∑' r : ℕ,
        (∑ loop : Fin (r + 1) → G.Dart,
          if kwGraphLoopExponent G loop = m then
            kwGraphLoopScalar G phase loop
          else 0) / ((r : ℂ) + 1)) / 2 := by
  unfold kwGraphFormalLogCoeff
  congr 2
  symm
  apply tsum_eq_sum
  intro r hr
  rw [Finset.mem_range, not_lt] at hr
  have hsum :
      (∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          kwGraphLoopScalar G phase loop
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro loop _
    rw [if_neg]
    intro heq
    have hdegree := kwGraphLoopExponent_totalDegree G loop
    rw [heq] at hdegree
    omega
  rw [hsum, zero_div]

@[simp] theorem kwGraphFormalLog_constantCoeff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) :
    MvPowerSeries.constantCoeff (kwGraphFormalLog G phase) = 0 := by
  change kwGraphFormalLogCoeff G phase 0 = 0
  simp [kwGraphFormalLogCoeff, ons_finsuppTotalDegree]

theorem kwGraphFormalLog_hasSubst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) :
    PowerSeries.HasSubst (kwGraphFormalLog G phase) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (kwGraphFormalLog_constantCoeff G phase)


end StatMech.FrontierA
