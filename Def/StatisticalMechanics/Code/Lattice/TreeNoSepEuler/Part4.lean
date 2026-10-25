/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
import Theorem.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part5
open SimpleGraph Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


def tnse_HasTreeFreeDetour (A : SimpleGraph V) (L : List (Sym2 V)) (e : Sym2 V) : Prop :=
  ∃ a b a' b' : V, e = s(a, b) ∧ s(a, b) ∈ A.edgeSet ∧
    A.Adj a a' ∧ A.Adj a' b' ∧ A.Adj b' b ∧
    s(a, a') ≠ s(a, b) ∧ s(a', b') ≠ s(a, b) ∧ s(b', b) ≠ s(a, b) ∧
    s(a, a') ∉ L ∧ s(a', b') ∉ L ∧ s(b', b) ∉ L


end Lattice
end StatMech
