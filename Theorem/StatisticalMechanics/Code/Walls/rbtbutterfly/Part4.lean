/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.WellFoundedSet
import Def.StatisticalMechanics.Code.Walls.rbtbutterfly.Part4
open Finset
open scoped BigOperators


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false


open Classical in


theorem rbt_partition_card {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    2 ^ m = (rbt_Red body T ∩ rbt_Yellow body T).card
      + (rbt_Ybar body T).card + (rbt_Rbar body T).card := by
  classical
  have hcard : (Finset.univ : Finset (rbt_Q m)).card = 2 ^ m := by
    simp [Finset.card_univ, Fintype.card_fin]
  rw [← hcard, rbt_Ybar, rbt_Rbar]
  
  have hU : (Finset.univ \ rbt_Yellow body T).card + (rbt_Yellow body T).card
      = (Finset.univ : Finset (rbt_Q m)).card :=
    Finset.card_sdiff_add_card_inter Finset.univ (rbt_Yellow body T) ▸ by
      rw [Finset.univ_inter]
  have hY : (rbt_Yellow body T \ rbt_Red body T).card
      + (rbt_Red body T ∩ rbt_Yellow body T).card = (rbt_Yellow body T).card := by
    have := Finset.card_sdiff_add_card_inter (rbt_Yellow body T) (rbt_Red body T)
    rwa [Finset.inter_comm (rbt_Yellow body T) (rbt_Red body T)] at this
  
  rw [← hU, ← hY]; ring

end StatMech.Walls.Reimer
