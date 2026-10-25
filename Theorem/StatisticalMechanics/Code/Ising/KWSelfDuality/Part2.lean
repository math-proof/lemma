/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.KWSelfDuality
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section HighTemp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] in


lemma incCount_insert (e : Sym2 V) (F : Finset (Sym2 V)) (he : e ∉ F) (v : V) :
    incCount (insert e F) v = incCount F v + (if v ∈ e then 1 else 0) := by
  unfold incCount
  rw [Finset.filter_insert]
  by_cases hv : v ∈ e
  · rw [if_pos hv, Finset.card_insert_of_notMem (by simp [he]), if_pos hv]
  · rw [if_neg hv, if_neg hv, add_zero]


end HighTemp
end Ising
end StatMech
