/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


theorem ofDartList_xFlux (l : List (ons_Dart L))
    (hbalanced : DartListBalanced l) :
    (ofDartList l hbalanced).xFlux (-1) =
      (l.map ons_xWrapSign).sum := by
  unfold xFlux ofDartList
  change (∑ y : ZMod L,
    (l.map (fun d => dartHorizontal d (-1, y))).sum) = _
  clear hbalanced
  induction l with
  | nil => simp
  | cons d l ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [dartHorizontal_xSeam_sum, ih]

theorem ofDartList_yFlux (l : List (ons_Dart L))
    (hbalanced : DartListBalanced l) :
    (ofDartList l hbalanced).yFlux (-1) =
      (l.map ons_yWrapSign).sum := by
  unfold yFlux ofDartList
  change (∑ x : ZMod L,
    (l.map (fun d => dartVertical d (x, -1))).sum) = _
  clear hbalanced
  induction l with
  | nil => simp
  | cons d l ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [dartVertical_ySeam_sum, ih]


theorem dartList_winding_det_eq_zero_of_locallyDisjoint
    (v : List (ons_Dart L)) (hv : DartListBalanced v)
    (w : List (ons_Dart L)) (hw : DartListBalanced w)
    (hdisj : (ofDartList v hv).LocallyDisjoint (ofDartList w hw)) :
    (v.map ons_xWrapSign).sum * (w.map ons_yWrapSign).sum -
      (v.map ons_yWrapSign).sum * (w.map ons_xWrapSign).sum = 0 := by
  have h := flux_det_eq_zero_of_locallyDisjoint hdisj
  rwa [ofDartList_xFlux, ofDartList_yFlux,
    ofDartList_xFlux, ofDartList_yFlux] at h

end IntegralSquareTorusCycle
end
end StatMech.FrontierD
