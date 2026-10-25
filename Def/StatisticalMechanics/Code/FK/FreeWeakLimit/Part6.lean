/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part5
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}


noncomputable def fullComponentEquivFree (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    (innerGraphFree d n ω ψ).ConnectedComponent ⊕ OutsideOnlyCompFree d n ψ ≃
      (fullGraphFree d n ω ψ).ConnectedComponent :=
  Equiv.ofBijective (fullComponentMapFree d n ω ψ)
    ⟨fullComponentMapFree_injective d n ω ψ, fullComponentMapFree_surjective d n ω ψ⟩


noncomputable def outsideShiftFree (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) : ℕ :=
  Nat.card (OutsideOnlyCompFree d n ψ)


end FK
end StatMech
