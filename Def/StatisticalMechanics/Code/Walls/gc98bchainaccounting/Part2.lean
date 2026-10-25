/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc98bchainaccounting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc87brerouteinjection.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc88brereroutehall.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc97bposnegreroute.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc98bchainaccounting
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


noncomputable def gc98b_cogRerouteImage (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    Finset (Finset ι × Finset ι) :=
  (m.powerset ×ˢ m.powerset).filter
    (fun LL => Disjoint LL.1 LL.2 ∧ sources ends LL.1 = (∅ : Finset W)
      ∧ (sources ends LL.2 = ({o, g} : Finset W) ∨ sources ends LL.2 = ({o, x} : Finset W)
        ∨ sources ends LL.2 = ({o, y} : Finset W))
      
      ∧ ∃ K₁ K₂ P : Finset ι, K₁ ⊆ m ∧ K₂ ⊆ m ∧ Disjoint K₁ K₂
          ∧ sources ends K₁ = ({o, g} : Finset W) ∧ sources ends K₂ = ({x, g} : Finset W)
          ∧ sources ends P = ({o, g} : Finset W)
          ∧ ((P ⊆ K₁ ∧ Disjoint P K₂ ∧ LL.1 = K₁ \ P ∧ LL.2 = K₂ ∪ P)
            ∨ (P ⊆ K₂ ∧ Disjoint P K₁ ∧ LL.1 = K₁ ∪ P ∧ LL.2 = K₂ \ P)))


end StatMech.Walls
