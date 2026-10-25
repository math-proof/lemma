/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.kwd_parityconfig
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Walls

section Cocycle

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {δ : Finset (Sym2 V)}

variable (G δ) in


def EvenOnAllCycles : Prop := ∀ (x : V) (p : G.Walk x x), walkPar G δ p = false


end Cocycle
end StatMech.Walls
