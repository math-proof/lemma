/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part11


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def lineFirstEndpointLeftToNoHit
    (n k : Nat) (start target : IsingLineBox n)
    (hk : 0 < k) (htarget : target.1 = 0) :
    IsingLineFirstEndpointFamily n k start target ->
      IsingHorizontalNoHitEndpointFamily (k - 1) 0 (-(start.1 : Int)) :=
  fun w => by
    let pref := w.1.dropLast
    let word := pref.reverse
    have hdata := lineFirstEndpoint_dropLast_data n k start target w hk
    dsimp only at hdata
    have hprefLen : pref.length = k - 1 := hdata.1
    have hprefEnd := (lineFirstEndpoint_left_dropLast n k start target
      w hk htarget).1
    have hprefSum :
        (start.1 : Int) + (pref.map endpointFailureLineStep).sum = 1 := by
      rw [← lineFreeEndpoint_eq_start_add_sum_endpointFailure]
      exact hprefEnd
    refine ⟨⟨word, ?_, ?_⟩, ?_⟩
    · simp [word, hprefLen]
    · intro r hr hhit
      have hrPref : r <= pref.length := by omega
      let cut := pref.length - r
      let a := pref.take cut
      let s := pref.drop cut
      have hcut : cut <= pref.length := Nat.sub_le _ _
      have hdecomp : a ++ s = pref := by
        exact List.take_append_drop cut pref
      have hsum :
          (pref.map endpointFailureLineStep).sum =
            (a.map endpointFailureLineStep).sum +
              (s.map endpointFailureLineStep).sum := by
        rw [← hdecomp, List.map_append, List.sum_append]
      have hpos := hdata.2.2 cut hcut
      have hposEq :
          lineFreeEndpoint (start.1 : Int) a =
            (start.1 : Int) + (a.map endpointFailureLineStep).sum :=
        lineFreeEndpoint_eq_start_add_sum_endpointFailure _ _
      have htake : word.take r = s.reverse := by
        dsimp [word, s, cut]
        rw [List.take_reverse]
      change lineFreeEndpoint (-1) (word.take r) = 0 at hhit
      rw [htake, lineFreeEndpoint_eq_start_add_sum_endpointFailure,
        sum_map_lineStep_reverse_endpointFailure] at hhit
      rw [hposEq] at hpos
      exact hpos.1 (by linarith)
    · dsimp [word]
      rw [lineFreeEndpoint_eq_start_add_sum_endpointFailure,
        sum_map_lineStep_reverse_endpointFailure]
      linarith

end
end StatMech.Universality
