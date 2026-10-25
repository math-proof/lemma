/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc10deltasupport
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V] [Fintype V]


noncomputable def gc10_partitionFunction (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun _ => True)


noncomputable def gc10_allConnMass (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)


noncomputable def gc10_allConnProb (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ) : ℝ :=
  gc10_allConnMass ends o x y g F / gc10_partitionFunction ends o x y g F


end StatMech.Walls
