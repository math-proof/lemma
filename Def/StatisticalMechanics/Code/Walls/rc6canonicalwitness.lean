/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6canonicalwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc5_minimalwitnessencoded
import Theorem.StatisticalMechanics.Code.Walls.rc6canonicalwitness
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*}

section Fintype

variable [Fintype E] [DecidableEq E]

variable {A B : Set (ConfigSpace E)} {ω : ConfigSpace E}


open Classical in


noncomputable def canonicalWitness (A B : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    Finset E × Finset E × Finset E :=
  if hω : ω ∈ disjointOccurrence A B then
    let p := exists_occursMinimalWitness hω
    (p.choose, p.choose_spec.choose, p.choose_spec.choose_spec.choose)
  else (∅, ∅, ∅)

end Fintype
end StatMech.Walls
