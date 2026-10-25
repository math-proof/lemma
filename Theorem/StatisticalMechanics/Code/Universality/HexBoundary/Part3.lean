/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Structure.StatisticalMechanics.Code.Universality.HexBoundary.Part2


namespace StatMech.Universality

open Complex Filter Topology

open scoped Topology Real BigOperators


namespace HexDomain

variable {V : Type*} [DecidableEq V] (D : HexDomain V)


omit [DecidableEq V] in


theorem interior_sum_zero (P : D.InteriorPairing) :
    ∑ e ∈ P.interior, D.incTerm e = 0 := by
  
  apply Finset.sum_involution (fun e _ => P.pair e)
  · 
    intro e he
    rw [P.cancel e he]; ring
  · 
    intro e he _; exact P.pair_ne e he
  · 
    intro e he; exact P.pair_mem e he
  · 
    intro e he; exact P.pair_invol e he


end HexDomain
end StatMech.Universality
