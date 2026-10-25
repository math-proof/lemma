/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part8
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


theorem dartHorizontal_xSeam_sum (d : ons_Dart L) :
    (∑ y : ZMod L, dartHorizontal d (-1, y)) = ons_xWrapSign d := by
  classical
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · by_cases hx : x = -1
    · subst x
      simp [dartHorizontal, pointMass, ons_xWrapSign, Prod.ext_iff]
    · simp [dartHorizontal, pointMass, ons_xWrapSign, Prod.ext_iff,
        hx, eq_comm]
  · simp [dartHorizontal, ons_xWrapSign]
  · by_cases hx : x = 0
    · subst x
      simp [dartHorizontal, pointMass, ons_xWrapSign, Prod.ext_iff]
    · simp [dartHorizontal, pointMass, ons_xWrapSign, Prod.ext_iff,
        hx, eq_comm]
  · simp [dartHorizontal, ons_xWrapSign]

theorem dartVertical_ySeam_sum (d : ons_Dart L) :
    (∑ x : ZMod L, dartVertical d (x, -1)) = ons_yWrapSign d := by
  classical
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · simp [dartVertical, ons_yWrapSign]
  · by_cases hy : y = -1
    · subst y
      simp [dartVertical, pointMass, ons_yWrapSign, Prod.ext_iff]
    · simp [dartVertical, pointMass, ons_yWrapSign, Prod.ext_iff,
        hy, eq_comm]
  · simp [dartVertical, ons_yWrapSign]
  · by_cases hy : y = 0
    · subst y
      simp [dartVertical, pointMass, ons_yWrapSign, Prod.ext_iff]
    · simp [dartVertical, pointMass, ons_yWrapSign, Prod.ext_iff,
        hy, eq_comm]

theorem ofDarts_xFlux {n : Nat} [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
    (ofDarts v hvalid).xFlux (-1) = ∑ k, ons_xWrapSign (v k) := by
  unfold xFlux ofDarts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact dartHorizontal_xSeam_sum (v k)

theorem ofDarts_yFlux {n : Nat} [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
    (ofDarts v hvalid).yFlux (-1) = ∑ k, ons_yWrapSign (v k) := by
  unfold yFlux ofDarts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact dartVertical_ySeam_sum (v k)


theorem dartLoop_winding_det_eq_zero_of_locallyDisjoint
    {n m : Nat} [NeZero n] [NeZero m]
    (v : Fin n → ons_Dart L)
    (hv : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (w : Fin m → ons_Dart L)
    (hw : ∀ k : Fin m,
      (w k).1 = ons_dirStep L (w (k + 1)).2 (w (k + 1)).1)
    (hdisj : (ofDarts v hv).LocallyDisjoint (ofDarts w hw)) :
    (∑ k, ons_xWrapSign (v k)) * (∑ k, ons_yWrapSign (w k)) -
      (∑ k, ons_yWrapSign (v k)) * (∑ k, ons_xWrapSign (w k)) = 0 := by
  have h := flux_det_eq_zero_of_locallyDisjoint hdisj
  rwa [ofDarts_xFlux, ofDarts_yFlux,
    ofDarts_xFlux, ofDarts_yFlux] at h


end IntegralSquareTorusCycle
end
end StatMech.FrontierD
