/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc91bglobalinjection.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.gc89bmetricinjection.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc90bperfiberinject.Part3
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


noncomputable def gc91b_cogxgPairs (ends : ι → Sym2 W) (m : Finset ι) (o x g : W) :
    Finset (Finset ι × Finset ι) :=
  (m.powerset ×ˢ m.powerset).filter
    (fun KK => Disjoint KK.1 KK.2 ∧ sources ends KK.1 = ({o, g} : Finset W)
      ∧ sources ends KK.2 = (∅ : Finset W) ∧ connK ends (m \ KK.1) x g)


noncomputable def gc91b_T3Pairs (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    Finset (Finset ι × Finset ι) :=
  (m.powerset ×ˢ m.powerset).filter
    (fun JJ => Disjoint JJ.1 JJ.2 ∧ sources ends JJ.1 = (∅ : Finset W)
      ∧ sources ends JJ.2 = (∅ : Finset W)
      ∧ connK ends (m \ JJ.1) o x ∧ connK ends (m \ JJ.1) o y ∧ connK ends (m \ JJ.1) o g)


end StatMech.Walls
