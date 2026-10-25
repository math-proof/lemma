/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6core.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


open Classical in


theorem rc7_reimerCardFormAll_iff_literal :
    ReimerCardFormAll ↔ ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
      #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B)) ≤
        #(Finset.univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ A ∧ (fun a => !ω a) ∈ B)) :=
  Iff.rfl


end StatMech.Walls
