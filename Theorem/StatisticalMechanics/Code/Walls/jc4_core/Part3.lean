/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc3_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc4_iteratecoincide
import Theorem.StatisticalMechanics.Code.Walls.jc4_tailnotprobed
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Def.StatisticalMechanics.Code.Walls.jc4_core.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc4_saturatingOrbitSplice_of_merge (h : jc4_SaturatingMerge) :
    jc3_SaturatingOrbitSplice := by
  intro K hK hge a hsat c len hframe
  exact jc4_splice_of_merge K a _ (h K hK hge a hsat c len hframe)


theorem jc4_saturatingEarMatch_of_merge (h : jc4_SaturatingMerge) :
    jc2_SaturatingEarMatch :=
  jc3_saturatingEarMatch_of_splice (jc4_saturatingOrbitSplice_of_merge h)


theorem jc4_balanceSaturatingContraction_of_merge (h : jc4_SaturatingMerge) :
    bpc_BalanceSaturatingContraction :=
  jc3_balanceSaturatingContraction_of_splice (jc4_saturatingOrbitSplice_of_merge h)


theorem jc4_balancePreservingContraction_of_merge (h : jc4_SaturatingMerge) :
    BalancePreservingContraction :=
  jc3_balancePreservingContraction_of_splice (jc4_saturatingOrbitSplice_of_merge h)


theorem jc4_starHull_totalTurn_eq_four_of_merge (h : jc4_SaturatingMerge)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  jc3_starHull_totalTurn_eq_four_of_splice (jc4_saturatingOrbitSplice_of_merge h) K hSK hne a


theorem jc4_degenerate_mergeDatum (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1)) (hne : r ≠ a.1.tail)
    (hne' : (K \ {r}).Nonempty) :
    jc4_MergeDatum K a r := by
  have hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1) :=
    fun i => jc3_notProbed_of_avoidsEarFootprint r _ (hfoot i)
  refine ⟨hne', ⟨a.1, jc4_basepoint_survives K a r hne⟩, 0, 0, dartOrbitPeriod K a,
    by rw [Nat.zero_add], ?_, ?_, ?_, ?_⟩
  · 
    rw [Nat.zero_add]; exact jc4_period_eq K a r hnp hne
  · 
    simp
  · 
    intro i _; simpa using hfoot i
  · 
    rw [jc_windowTurn_eq, jc_windowTurn_eq, umEar_windowTurn_self, umEar_windowTurn_self]


theorem jc4_farCell_mergeDatum (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1))
    (hr : r ∉ bpc_orbitFootprint K a) (hne' : (K \ {r}).Nonempty) :
    jc4_MergeDatum K a r :=
  jc4_degenerate_mergeDatum K a r hfoot (bpc_ne_tail_of_not_footprint K a r hr) hne'


theorem jc4_degenerate_merge_gives_splice (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1)) (hne : r ≠ a.1.tail)
    (hne' : (K \ {r}).Nonempty) :
    jc3_OrbitSpliceDatum K a r :=
  jc4_splice_of_merge K a r (jc4_degenerate_mergeDatum K a r hfoot hne hne')


end Walls
end StatMech
