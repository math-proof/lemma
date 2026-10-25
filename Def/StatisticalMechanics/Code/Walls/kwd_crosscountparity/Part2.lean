/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Walls.kwd_crosscountparity
open Finset Set SimpleGraph
open StatMech.Lattice


namespace StatMech.Walls

def kwd_sideBoundary {V : Type*} (S : V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun x y => S x != S y, by
    intro x y
    simp only
    cases S x <;> cases S y <;> rfl⟩

end StatMech.Walls
