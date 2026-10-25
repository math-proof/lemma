/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.kwd_parityconfig.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Walls

section Cocycle

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {δ : Finset (Sym2 V)}

theorem walkPar_eq_of_evenOnAllCycles (hev : EvenOnAllCycles G δ) {x y : V}
    (p q : G.Walk x y) : walkPar G δ p = walkPar G δ q := by
  have hclosed : walkPar G δ (p.append q.reverse) = false := hev _ _
  rw [walkPar_append, walkPar_reverse] at hclosed
  revert hclosed
  cases walkPar G δ p <;> cases walkPar G δ q <;> simp

end Cocycle
end StatMech.Walls
