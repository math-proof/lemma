/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.CliqueNumber
set_option maxHeartbeats 400000

open scoped Classical
open Finset BigOperators Filter Topology


namespace CliqueNumber

/-- In a Boolean algebra, if $H \le a$ and $K \le a^c$, then $(H \sqcup K) \sqcap a = H$. -/
lemma ba_sup_inf_right {α : Type*} [BooleanAlgebra α] {a H K : α}
    (hH : H ≤ a) (hK : K ≤ aᶜ) : (H ⊔ K) ⊓ a = H := by
  rw [inf_sup_right, le_bot_iff.mp (le_trans (inf_le_inf_right a hK) (by simp)),
    inf_of_le_left hH, sup_bot_eq]

/-- In a Boolean algebra, if $H \le a$ and $K \le a^c$, then $(H \sqcup K) \sqcap a^c = K$. -/
lemma ba_sup_inf_compl {α : Type*} [BooleanAlgebra α] {a H K : α}
    (hH : H ≤ a) (hK : K ≤ aᶜ) : (H ⊔ K) ⊓ aᶜ = K := by
  rw [inf_sup_right, le_bot_iff.mp (le_trans (inf_le_inf_right aᶜ hH) (by simp)),
    inf_of_le_left hK, bot_sup_eq]

end CliqueNumber
