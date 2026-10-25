/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

noncomputable def poc_slabBox (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    Finset (ConfigSpace α) :=
  Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧
    orbitKey (ω, poc_keyFlip k ω) = k)

open Classical in


noncomputable def poc_slabImg (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    Finset (ConfigSpace α) :=
  Finset.univ.filter (fun ω => ω ∈ A ∧ poc_keyFlip k ω ∈ B ∧
    orbitKey (ω, poc_keyFlip k ω) = k)


end StatMech
