/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part4
import Def.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem endpointMirrorBoundaryPair_mass_nonneg
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    (heading : V → Fin 3 → ℤ)
    (hobs : ∀ z, D.obs z =
      endpointParafObservable R.inRegion R.start h0 z (5 / 8) hexChi)
    (eNeg ePos : HexIncidence V) (hne : eNeg ≠ ePos)
    (headNeg headPos : ℤ)
    (hHeadNeg : heading eNeg.vtx eNeg.edge = headNeg)
    (hHeadPos : heading ePos.vtx ePos.edge = headPos)
    (hmidPos : D.mid ePos.vtx ePos.edge =
      hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
    (hsym : ∀ m, R.inRegion m → R.inRegion (hsc_refl R.start h0 m))
    (W : ℝ)
    (hdetNeg : ∀ ts,
      (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt
            (D.mid eNeg.vtx eNeg.edge) →
        (ofTurns R.start h0 ts).turning = W)
    (htilt : hexPhase_sideTilt headPos = -hexPhase_sideTilt headNeg) :
    0 ≤ (endpointMirrorBoundaryPair_of_reflection heading hobs eNeg ePos
      hne headNeg headPos hHeadNeg hHeadPos hmidPos hsym W hdetNeg htilt).mass := by
  change 0 ≤ endpointCountObservable R.inRegion R.start h0
    (D.mid eNeg.vtx eNeg.edge) hexChi
  unfold endpointCountObservable
  exact tsum_nonneg (endpointCountWeight_nonneg R.inRegion R.start h0
    (D.mid eNeg.vtx eNeg.edge) hexChi_pos.le)


end
end StatMech.Universality
