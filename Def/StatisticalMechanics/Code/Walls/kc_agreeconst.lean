/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_agreeconst.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Walls

section EdgeBoundary

variable {V : Type*} {G : SimpleGraph V} (S : Set V)


def crossesBoundary (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun u v => (u ∈ S) ≠ (v ∈ S), by
    intro a b; exact propext ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩⟩ e

end EdgeBoundary
end StatMech.Walls
