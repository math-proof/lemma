/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardReversibleCycleCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u

open StatMech.Onsager


theorem kwGraphLoop_nonbacktracking_of_scalar_ne_zero
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hscalar : kwGraphLoopScalar G phase loop ≠ 0) :
    kwGraphLoopNonbacktracking G loop := by
  intro k
  have hfactor : kwGraphTransition G (fun _ ↦ 1) phase
      (loop k) (loop (k + 1)) ≠ 0 := by
    intro hzero
    apply hscalar
    unfold kwGraphLoopScalar
    exact Finset.prod_eq_zero (Finset.mem_univ k) hzero
  by_cases hstep : (loop k).snd = (loop (k + 1)).fst ∧
      (loop k).edge ≠ (loop (k + 1)).edge
  · exact hstep
  · unfold kwGraphTransition at hfactor
    rw [if_neg hstep] at hfactor
    exact (hfactor rfl).elim


end StatMech.FrontierA
