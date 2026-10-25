/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwGraphLoopExponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) : Sym2 V →₀ ℕ :=
  ∑ k, Finsupp.single (loop k).edge 1


noncomputable def kwGraphLoopScalar
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) : ℂ :=
  ∏ k, kwGraphTransition G (fun _ ↦ 1) phase (loop k) (loop (k + 1))

end StatMech.FrontierA
