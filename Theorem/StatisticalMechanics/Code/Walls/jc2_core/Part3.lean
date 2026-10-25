/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc2_engine
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinpendant
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinconn
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinthickdichotomy.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc_core
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Def.StatisticalMechanics.Code.Walls.jc2_core.Part3
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc2_balanceSaturatingContraction_of_earMatch
    (h : jc2_SaturatingEarMatch) : bpc_BalanceSaturatingContraction := by
  intro K hK hge a hsat
  
  have hne : K.Nonempty := by
    rw [← Set.ncard_pos hK]; omega
  obtain ⟨c, len, hframe⟩ := jc2_runFrame K hK hne
  
  set r : Site 2 := c + ![len, 0] with hr
  have hrK : r ∈ K := hframe.isRun.run_mem len hframe.isRun.len_nonneg (le_refl len)
  
  have hmatch : jc2_PendantClipMatch K a r := h K hK hge a hsat c len hframe
  exact jc2_contraction_of_pendantClipMatch K hK a r hrK hmatch


theorem jc2_balancePreservingContraction_of_earMatch
    (h : jc2_SaturatingEarMatch) : BalancePreservingContraction :=
  bpc_balancePreservingContraction_of_saturating
    (jc2_balanceSaturatingContraction_of_earMatch h)


theorem jc2_turningIsFullRevolution_of_earMatch (h : jc2_SaturatingEarMatch)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_contraction (jc2_balancePreservingContraction_of_earMatch h)
    K hK hne a


theorem jc2_starHull_turningIsFullRevolution_of_earMatch (h : jc2_SaturatingEarMatch)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  gbe_totalTurn_eq_four_of_contraction K hSK hne a
    (jc2_balancePreservingContraction_of_earMatch h)


theorem jc2_starHull_totalTurn_eq_four_of_earMatch (h : jc2_SaturatingEarMatch)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  jc2_starHull_turningIsFullRevolution_of_earMatch h K hSK hne a


theorem jc2_saturating_has_runFrame (K : Set (Site 2)) (hK : K.Finite) (hge : 2 ≤ K.ncard) :
    ∃ c len, jc2_RunFrame K c len := by
  have hne : K.Nonempty := by rw [← Set.ncard_pos hK]; omega
  exact jc2_runFrame K hK hne


theorem jc2_runFrame_thinThickDichotomy (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hframe : jc2_RunFrame K c len) : jc2_ThinThickDichotomy K c len :=
  jc2_thinThickDichotomy K c len hframe.isRun


theorem jc2_thin_book_ear_cellConnected (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hconn : CellConnected K) (hframe : jc2_RunFrame K c len) (hlen : 1 ≤ len)
    (hthin : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
    CellConnected (K \ {(c + ![len, 0] : Site 2)}) :=
  jc2_thinFingerClip_cellConnected K c len hconn hframe.isRun hlen hthin


theorem jc2_unitCell_core_balanceIsFour : BalanceIsFour unitCell ucBase :=
  jc_unitCell_core_balanceIsFour


theorem jc2_domino_core_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase :=
  jc_domino_core_witness


theorem jc2_domino_book_ear : jc2_RunFrame domino (![0, 0] : Site 2) 1 :=
  jc2_domino_runFrame


theorem jc2_domino_thin_book_ear : jc_IsPendantCell domino ((![0, 0] : Site 2) + ![1, 0]) :=
  jc_domino_rightEnd_pendant


end Walls
end StatMech
