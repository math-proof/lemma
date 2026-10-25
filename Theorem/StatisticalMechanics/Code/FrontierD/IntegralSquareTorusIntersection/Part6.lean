/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part6
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


theorem pointMass_west (a p : ZMod L × ZMod L) :
    pointMass a (p.1 - 1, p.2) = pointMass (a.1 + 1, a.2) p := by
  unfold pointMass
  congr 1
  apply propext
  simp only [Prod.ext_iff]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨by rw [← hx]; ring, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨by rw [hx]; ring, hy⟩

theorem pointMass_south (a p : ZMod L × ZMod L) :
    pointMass a (p.1, p.2 - 1) = pointMass (a.1, a.2 + 1) p := by
  unfold pointMass
  congr 1
  apply propext
  simp only [Prod.ext_iff]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hx, by rw [← hy]; ring⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, by rw [hy]; ring⟩


end IntegralSquareTorusCycle
end
end StatMech.FrontierD
