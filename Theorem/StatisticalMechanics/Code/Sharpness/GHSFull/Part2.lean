/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Def.StatisticalMechanics.Code.Sharpness.GHSFull.Part2
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


namespace StatMech

namespace Sharpness

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem spin_flipCfg (s : ConfigSpace V) (x : V) : spin (flipCfg s) x = - spin s x := by
  unfold flipCfg spin; cases h : s x <;> simp [h]


theorem bond_flipCfg (s : ConfigSpace V) (e : Sym2 V) : bond (flipCfg s) e = bond s e := by
  induction e with
  | h a b =>
    rw [bond_mk, bond_mk]; unfold flipCfg spin
    cases ha : s a <;> cases hb : s b <;> simp [ha, hb]


end Sharpness
end StatMech
