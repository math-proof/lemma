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
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part3
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


noncomputable def IsOutsideOnlyFree (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    (outsideOpenGraph d n ψ).ConnectedComponent → Prop :=
  ConnectedComponent.lift (OutsideOnlyFree d n ψ)
    (fun a b p _ => propext ⟨fun h => outsideOnlyFree_of_reachable d n ψ h p.reachable,
      fun h => outsideOnlyFree_of_reachable d n ψ h p.reachable.symm⟩)

end FK
end StatMech
