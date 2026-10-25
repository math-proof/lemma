/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Structure.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def poc_swapSel (A B : Set (ConfigSpace α)) (W : poc_WitnessData A B) :
    ConfigSpace α × ConfigSpace α → (α → Bool) :=
  fun p => fun a => !(W.wK p.1 a)


def poc_WitnessInjection (A B : Set (ConfigSpace α)) : Prop :=
  ∃ W : poc_WitnessData A B,
    Set.InjOn (swapPair (poc_swapSel A B W))
      {p : ConfigSpace α × ConfigSpace α | p.1 ∈ disjointOccurrence A B}


end StatMech
