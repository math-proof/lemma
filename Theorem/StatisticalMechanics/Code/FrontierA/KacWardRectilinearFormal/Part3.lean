/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


theorem kwGraphFormalBucket_eval_eq_loopSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ) (r : ℕ) :
    (∑' m : Sym2 V →₀ ℕ,
      (∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          kwGraphLoopScalar G phase loop
        else 0) * ons_mvMonomialValue weight m) =
      ∑ loop : Fin (r + 1) → G.Dart,
        ons_loopWeight (kwGraphTransition G weight phase) loop := by
  rw [ons_tsum_finite_exponent_buckets]
  apply Finset.sum_congr rfl
  intro loop _
  exact (kwGraphLoopWeight_factor G weight phase loop).symm

theorem kwGraphFormalBucket_eval_div_eq_loopSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (weight : Sym2 V → ℂ) (r : ℕ) :
    (∑' m : Sym2 V →₀ ℕ,
      ((∑ loop : Fin (r + 1) → G.Dart,
        if kwGraphLoopExponent G loop = m then
          kwGraphLoopScalar G phase loop
        else 0) / ((r : ℂ) + 1)) * ons_mvMonomialValue weight m) =
      (∑ loop : Fin (r + 1) → G.Dart,
        ons_loopWeight (kwGraphTransition G weight phase) loop) /
          ((r : ℂ) + 1) := by
  rw [← kwGraphFormalBucket_eval_eq_loopSum G phase weight r]
  rw [← tsum_div_const]
  apply tsum_congr
  intro m
  ring

end StatMech.FrontierA
