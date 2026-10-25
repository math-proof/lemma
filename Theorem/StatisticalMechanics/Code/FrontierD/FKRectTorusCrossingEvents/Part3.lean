/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectVerticalCrossingEvent_eq_finiteEndpointUnion
    (R : FKRectTorus) (x0 x1 y0 y1 : Nat) :
    fkRectVerticalCrossingEvent R x0 x1 y0 y1 =
      fkRectFiniteEventUnion
        (fkRectVerticalEndpointPairs R x0 x1 y0 y1)
        (fkRectVerticalEndpointConnectionEvent R x0 x1 y0 y1) := by
  ext omega
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨(x, y), by simp [fkRectVerticalEndpointPairs, hx, hy], hxy⟩
  · rintro ⟨p, hp, hconn⟩
    have hend : p.1.1.2.val = y0 ∧ p.2.1.2.val = y1 := by
      simpa [fkRectVerticalEndpointPairs] using hp
    exact ⟨p.1, p.2, hend.1, hend.2, hconn⟩

theorem fkRectVerticalEndpointPairs_nonempty
    (R : FKRectTorus) (x0 x1 y0 y1 : Nat)
    (hxx : x0 ≤ x1) (hx1 : x1 < R.width)
    (hyy : y0 ≤ y1) (hy1 : y1 < R.height) :
    (fkRectVerticalEndpointPairs R x0 x1 y0 y1).Nonempty := by
  let xb : R.Vertex := (⟨x0, hxx.trans_lt hx1⟩, ⟨y0, hyy.trans_lt hy1⟩)
  let xt : R.Vertex := (⟨x0, hxx.trans_lt hx1⟩, ⟨y1, hy1⟩)
  have hxb : xb ∈ fkRectVertexRectangle R x0 x1 y0 y1 := by
    simp [xb, fkRectVertexRectangle, hxx, hyy]
  have hxt : xt ∈ fkRectVertexRectangle R x0 x1 y0 y1 := by
    simp [xt, fkRectVertexRectangle, hxx, hyy]
  refine ⟨(⟨xb, hxb⟩, ⟨xt, hxt⟩), ?_⟩
  simp [fkRectVerticalEndpointPairs, xb, xt]


theorem exists_verticalEndpoint_eventMass_ge
    (R : FKRectTorus) {q c : Real} (hq : 0 < q)
    (x0 x1 y0 y1 : Nat)
    (hxx : x0 ≤ x1) (hx1 : x1 < R.width)
    (hyy : y0 ≤ y1) (hy1 : y1 < R.height)
    (hc : c ≤ fkRectCriticalEventMass R q
      (fkRectVerticalCrossingEvent R x0 x1 y0 y1)) :
    ∃ p ∈ fkRectVerticalEndpointPairs R x0 x1 y0 y1,
      c ≤ ((fkRectVerticalEndpointPairs R x0 x1 y0 y1).card : Real) *
        fkRectCriticalEventMass R q
          (fkRectVerticalEndpointConnectionEvent R x0 x1 y0 y1 p) := by
  rw [fkRectVerticalCrossingEvent_eq_finiteEndpointUnion] at hc
  exact exists_card_mul_eventMass_ge_of_finiteUnion_ge R hq
    (fkRectVerticalEndpointPairs_nonempty R x0 x1 y0 y1
      hxx hx1 hyy hy1)
    (fkRectVerticalEndpointConnectionEvent R x0 x1 y0 y1) hc

end
end StatMech.FrontierD
