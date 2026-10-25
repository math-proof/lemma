/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


@[simp] theorem kwGraphLoopExponent_totalDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    ons_finsuppTotalDegree (kwGraphLoopExponent G loop) = n := by
  unfold kwGraphLoopExponent
  rw [ons_finsuppTotalDegree_finset_sum]
  simp

theorem kwGraphTransition_entry_factor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (dart next : G.Dart) :
    kwGraphTransition G weight phase dart next =
      kwGraphTransition G (fun _ ↦ 1) phase dart next * weight dart.edge := by
  unfold kwGraphTransition
  split
  · ring
  · simp_all

theorem kwGraphLoopWeight_factor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    ons_loopWeight (kwGraphTransition G weight phase) loop =
      kwGraphLoopScalar G phase loop *
        (kwGraphLoopExponent G loop).prod
          (fun edge k ↦ weight edge ^ k) := by
  unfold ons_loopWeight kwGraphLoopScalar kwGraphLoopExponent
  rw [Finset.prod_congr rfl (fun k _ ↦
    kwGraphTransition_entry_factor G weight phase (loop k) (loop (k + 1)))]
  rw [Finset.prod_mul_distrib, ons_finsuppProd_sum_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [Finsupp.prod_single_index] <;> simp


end StatMech.FrontierA
