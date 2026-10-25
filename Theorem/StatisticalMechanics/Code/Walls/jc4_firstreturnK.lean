/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_firstreturnK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
import Def.StatisticalMechanics.Code.Walls.jc4_firstreturnK
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc4_iterate_period_eq (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartNext K)^[dartOrbitPeriod K a] a.1 = a.1 := by
  have := dartOrbitPeriod_iterate K a
  have hv := congrArg Subtype.val this
  rwa [dartNextSub_iterate_val] at hv


theorem jc4_firstReturn_exists_of_some_free (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (j : ℕ) (hj : jc4_FootprintFree K a r j) :
    ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · 
    refine ⟨dartOrbitPeriod K a, dartOrbitPeriod_pos K hK a, ?_⟩
    unfold jc4_FootprintFree at hj ⊢
    rw [jc4_iterate_period_eq K a]
    subst hj0
    simpa using hj
  · 
    exact ⟨j, hjpos, hj⟩


end Walls
end StatMech
