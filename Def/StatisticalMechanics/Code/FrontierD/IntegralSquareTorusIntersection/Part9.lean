/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part8
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def DartListBalanced (l : List (ons_Dart L)) : Prop :=
  ∀ p : ZMod L × ZMod L,
    (l.map (fun d => pointMass d.1 p)).sum =
      (l.map (fun d => pointMass (ons_dirStep L d.2 d.1) p)).sum


def ofDartList (l : List (ons_Dart L)) (hbalanced : DartListBalanced l) :
    IntegralSquareTorusCycle L where
  horizontal p := (l.map (fun d => dartHorizontal d p)).sum
  vertical p := (l.map (fun d => dartVertical d p)).sum
  divergence_zero p := by
    calc
      (l.map (fun d => dartHorizontal d p)).sum +
            (l.map (fun d => dartVertical d p)).sum -
          (l.map (fun d => dartHorizontal d (p.1 - 1, p.2))).sum -
          (l.map (fun d => dartVertical d (p.1, p.2 - 1))).sum =
        (l.map (fun d =>
          dartHorizontal d p + dartVertical d p -
            dartHorizontal d (p.1 - 1, p.2) -
            dartVertical d (p.1, p.2 - 1))).sum := by
          have hcombine : ∀ l' : List (ons_Dart L),
              (l'.map (fun d => dartHorizontal d p)).sum +
                    (l'.map (fun d => dartVertical d p)).sum -
                  (l'.map (fun d =>
                    dartHorizontal d (p.1 - 1, p.2))).sum -
                  (l'.map (fun d =>
                    dartVertical d (p.1, p.2 - 1))).sum =
                (l'.map (fun d =>
                  dartHorizontal d p + dartVertical d p -
                    dartHorizontal d (p.1 - 1, p.2) -
                    dartVertical d (p.1, p.2 - 1))).sum := by
            intro l'
            induction l' with
            | nil => simp
            | cons d l' ih =>
                simp only [List.map_cons, List.sum_cons] at ih ⊢
                linear_combination ih
          exact hcombine l
      _ = (l.map (fun d => pointMass d.1 p -
          pointMass (ons_dirStep L d.2 d.1) p)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro d _
            exact dart_divergence d p
      _ = 0 := by
        have hsub : ∀ l' : List (ons_Dart L),
            (l'.map (fun d => pointMass d.1 p -
                pointMass (ons_dirStep L d.2 d.1) p)).sum =
              (l'.map (fun d => pointMass d.1 p)).sum -
                (l'.map (fun d =>
                  pointMass (ons_dirStep L d.2 d.1) p)).sum := by
          intro l'
          induction l' with
          | nil => simp
          | cons d l' ih =>
              simp only [List.map_cons, List.sum_cons] at ih ⊢
              linear_combination ih
        rw [hsub l]
        rw [hbalanced p, sub_self]

end IntegralSquareTorusCycle
end
end StatMech.FrontierD
