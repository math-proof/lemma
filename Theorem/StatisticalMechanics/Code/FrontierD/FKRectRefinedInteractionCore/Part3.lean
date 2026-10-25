/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

theorem fkRectRefinedRawInteraction_append_left
    (a b c : List (ons_Dart L)) :
    fkRectRefinedRawInteraction (a ++ b) c =
      fkRectRefinedRawInteraction a c +
        fkRectRefinedRawInteraction b c := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [List.map_append, List.sum_append, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem fkRectRefinedRawInteraction_append_right
    (a b c : List (ons_Dart L)) :
    fkRectRefinedRawInteraction a (b ++ c) =
      fkRectRefinedRawInteraction a b +
        fkRectRefinedRawInteraction a c := by
  classical
  unfold fkRectRefinedRawInteraction
  simp only [List.map_append, List.sum_append, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem fkRectRefinedRawInteraction_eq_intersection
    (a b : List (ons_Dart L))
    (ha : DartListBalanced a) (hb : DartListBalanced b) :
    fkRectRefinedRawInteraction a b =
      (ofDartList a ha).intersection (ofDartList b hb) :=
  rfl

theorem fkRectRefinedRawInteraction_eq_wrap_det
    (a b : List (ons_Dart L))
    (ha : DartListBalanced a) (hb : DartListBalanced b) :
    fkRectRefinedRawInteraction a b =
      (a.map ons_xWrapSign).sum * (b.map ons_yWrapSign).sum -
        (a.map ons_yWrapSign).sum * (b.map ons_xWrapSign).sum := by
  rw [fkRectRefinedRawInteraction_eq_intersection a b ha hb,
    IntegralSquareTorusCycle.intersection_eq_flux_det,
    IntegralSquareTorusCycle.ofDartList_xFlux,
    IntegralSquareTorusCycle.ofDartList_yFlux,
    IntegralSquareTorusCycle.ofDartList_xFlux,
    IntegralSquareTorusCycle.ofDartList_yFlux]


end
end StatMech.FrontierD
