/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part5
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


structure poc_WitnessData (A B : Set (ConfigSpace α)) where
  
  wK : ConfigSpace α → (α → Bool)
  
  wL : ConfigSpace α → (α → Bool)
  
  occA : ∀ ω, ω ∈ disjointOccurrence A B → OccursOn A {a | wK ω a = true} ω
  
  occB : ∀ ω, ω ∈ disjointOccurrence A B → OccursOn B {a | wL ω a = true} ω
  
  disj : ∀ ω, ω ∈ disjointOccurrence A B → ∀ a, wK ω a = true → wL ω a = false


end StatMech
