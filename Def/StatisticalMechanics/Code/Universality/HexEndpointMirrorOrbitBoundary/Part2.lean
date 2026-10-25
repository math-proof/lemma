/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def endpointFixedBoundaryPoint_of_winding
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    (heading : V → Fin 3 → ℤ)
    (hobs : ∀ z, D.obs z =
      endpointParafObservable R.inRegion R.start h0 z (5 / 8) hexChi)
    (e : HexIncidence V) (head : ℤ)
    (hHead : heading e.vtx e.edge = head)
    (W : ℝ)
    (hdet : ∀ ts,
      (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt (D.mid e.vtx e.edge) →
        (ofTurns R.start h0 ts).turning = W)
    (hphase : hexPhase_sideTilt head = -(5 / 8 : ℝ) * W) :
    HexFixedBoundaryPoint D heading where
  incidence := e
  head := head
  hHead := hHead
  mass := endpointCountObservable R.inRegion R.start h0
    (D.mid e.vtx e.edge) hexChi
  mass_nonneg := by
    unfold endpointCountObservable
    exact tsum_nonneg (endpointCountWeight_nonneg R.inRegion R.start h0
      (D.mid e.vtx e.edge) hexChi_pos.le)
  phase := by
    rw [hobs,
      endpointParafObservable_factor R.inRegion R.start h0
        (D.mid e.vtx e.edge) (5 / 8) hexChi W hdet]
    congr 2
    rw [hphase]
    push_cast
    ring


end
end StatMech.Universality
