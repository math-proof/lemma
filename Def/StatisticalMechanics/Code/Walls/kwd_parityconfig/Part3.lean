/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.kwd_parityconfig.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Walls

section Disagree

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def disagree (c : V → Bool) : Finset (Sym2 V) :=
  G.edgeFinset.filter
    (fun e => Sym2.lift ⟨fun x y => decide (c x ≠ c y),
      by intro x y; rw [decide_eq_decide]; exact ne_comm⟩ e)

end Disagree
end StatMech.Walls
