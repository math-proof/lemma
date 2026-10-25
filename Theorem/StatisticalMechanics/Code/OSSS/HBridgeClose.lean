/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/HBridgeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.OSFKAssemblyClose
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Def.StatisticalMechanics.Code.OSSS.HBridgeClose
open scoped BigOperators Classical
open Finset Real Set Filter Topology


namespace StatMech

namespace OSSS

namespace HBridgeClose

open StatMech.FK

open StatMech.OSSS.OSFKAssemblyClose

open StatMech.OSSS.BetaCMatch

variable {V : Type*} [Fintype V] [DecidableEq V]


@[simp] theorem flipE_self (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    flipE e ω e = !ω e := by unfold flipE; simp

theorem flipE_of_ne {e e' : Sym2 V} (h : e' ≠ e) (ω : ConfigSpace (Sym2 V)) :
    flipE e ω e' = ω e' := by unfold flipE; rw [Function.update_of_ne h]


theorem flipE_flipE (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : flipE e (flipE e ω) = ω := by
  funext e'
  by_cases h : e' = e
  · subst h; simp
  · rw [flipE_of_ne h, flipE_of_ne h]


end HBridgeClose
end OSSS
end StatMech
