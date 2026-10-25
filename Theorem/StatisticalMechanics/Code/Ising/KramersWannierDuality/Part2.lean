/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Def.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part2
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section Computable

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in

theorem cutEdges_eq_cutEdgesB (s : ConfigSpace V) :
    cutEdges G s = cutEdgesB G s := by
  unfold cutEdges cutEdgesB
  apply Finset.filter_congr
  intro e _
  induction e using Sym2.ind with
  | _ x y =>
    rw [bond_mk]; unfold spin edgeDiff
    simp only [Sym2.lift_mk]
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy] <;> norm_num


end Computable
end Ising
end StatMech
