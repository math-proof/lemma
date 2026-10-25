/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part5
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


@[simp] theorem kwg_isSplit_mk {V : Type*} (c : V → Bool) (x y : V) :
    kwg_isSplit c s(x, y) ↔ c x ≠ c y := Iff.rfl

theorem kwg_isSplit_iff_bond_neg {V : Type*} (c : ConfigSpace V) (e : Sym2 V) :
    kwg_isSplit c e ↔ bond c e = -1 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [kwg_isSplit_mk, bond_mk]
      unfold spin
      cases c x <;> cases c y <;> norm_num

end Ising
end StatMech
