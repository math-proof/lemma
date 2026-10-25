/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentSingletonMixing
import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK


noncomputable def extendLatticeLocalPattern (d : Nat)
    (S : Finset (Sym2 (Site d)))
    (a : ↑(latticeEdgePart d S) -> Nat) : ↑S -> Nat :=
  fun e => if he : e.1 ∈ latticeEdgePart d S then a ⟨e.1, he⟩ else 0


noncomputable def latticeReducedPatternSet (d : Nat)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S -> Nat)) :
    Set (↑(latticeEdgePart d S) -> Nat) :=
  {a | extendLatticeLocalPattern d S a ∈ A}

end StatMech.FrontierB
