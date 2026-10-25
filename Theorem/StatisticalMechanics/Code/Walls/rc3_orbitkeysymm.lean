/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_orbitkeysymm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*}


theorem rc3_orbitKey_symm (a b : ConfigSpace α) :
    orbitKey (a, b) = orbitKey (b, a) := by
  simp only [orbitKey]
  apply Prod.ext <;> funext c <;> simp only [Bool.or_comm, Bool.and_comm]


theorem rc3_orbitKey_swap (p : ConfigSpace α × ConfigSpace α) :
    orbitKey (p.2, p.1) = orbitKey p := by
  rw [rc3_orbitKey_symm]

end StatMech.Walls
