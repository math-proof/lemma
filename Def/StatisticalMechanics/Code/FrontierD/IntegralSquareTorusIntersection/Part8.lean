/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part7
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def ofDarts {n : Nat} [NeZero n] (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
    IntegralSquareTorusCycle L where
  horizontal p := ∑ k, dartHorizontal (v k) p
  vertical p := ∑ k, dartVertical (v k) p
  divergence_zero p := by
    rw [show (∑ k, dartHorizontal (v k) p) +
          (∑ k, dartVertical (v k) p) -
          (∑ k, dartHorizontal (v k) (p.1 - 1, p.2)) -
          (∑ k, dartVertical (v k) (p.1, p.2 - 1)) =
        ∑ k, (dartHorizontal (v k) p + dartVertical (v k) p -
          dartHorizontal (v k) (p.1 - 1, p.2) -
          dartVertical (v k) (p.1, p.2 - 1)) by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]]
    simp_rw [dart_divergence]
    have hshift :
        (∑ k, pointMass (ons_dirStep L (v k).2 (v k).1) p) =
          ∑ k, pointMass (v k).1 p := by
      calc
        (∑ k, pointMass (ons_dirStep L (v k).2 (v k).1) p) =
            ∑ k, pointMass
              (ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) p := by
                simpa using
                  (Equiv.sum_comp (Equiv.addRight (1 : Fin n))
                    (fun k => pointMass
                      (ons_dirStep L (v k).2 (v k).1) p)).symm
        _ = ∑ k, pointMass (v k).1 p := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← hvalid k]
    rw [Finset.sum_sub_distrib, hshift, sub_self]

end IntegralSquareTorusCycle
end
end StatMech.FrontierD
