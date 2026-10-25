/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.FK.InducedBC
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


noncomputable def outsideOpenGraph (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    SimpleGraph (boxVerts d (n+1)) where
  Adj x y := (boxGraph d (n+1)).Adj x y ∧ ψ s(x, y) = true ∧ s(x, y) ∉ Set.range (innerEdge d n)
  symm := by
    constructor
    rintro x y ⟨hadj, hopen, hrange⟩
    refine ⟨hadj.symm, ?_, ?_⟩ <;> rw [Sym2.eq_swap] <;> assumption
  loopless := ⟨by rintro x ⟨hadj, _, _⟩; exact hadj.ne rfl⟩

end FK
end StatMech
