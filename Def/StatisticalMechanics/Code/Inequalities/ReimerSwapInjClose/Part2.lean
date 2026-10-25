/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

noncomputable def boxOrbit (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    Finset (ConfigSpace α × ConfigSpace α) :=
  Finset.univ.filter (fun p => p.1 ∈ disjointOccurrence A B ∧ orbitKey p = k)

open Classical in

noncomputable def imgOrbit (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    Finset (ConfigSpace α × ConfigSpace α) :=
  Finset.univ.filter (fun q => q.1 ∈ A ∧ q.2 ∈ B ∧ orbitKey q = k)


def PerOrbitCard (A B : Set (ConfigSpace α)) : Prop :=
  ∀ k : ConfigSpace α × ConfigSpace α, #(boxOrbit A B k) ≤ #(imgOrbit A B k)


end StatMech
