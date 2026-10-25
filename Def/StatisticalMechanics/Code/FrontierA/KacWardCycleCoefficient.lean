/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager

universe u


noncomputable def kwGraphSquarefreeLoopFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V)) :
    Finset (Fin n → G.Dart) :=
  Finset.univ.filter fun loop ↦
    kwGraphLoopExponent G loop = ons_finsetExponent S ∧
      kwGraphLoopScalar G phase loop ≠ 0

end StatMech.FrontierA
