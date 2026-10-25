/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


noncomputable def hexFixedBoundaryPoint_of_winding
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P)
    (heading : V → Fin 3 → ℤ)
    (e : HexIncidence V) (head : ℤ)
    (hHead : heading e.vtx e.edge = head)
    (W : ℝ)
    (hdet : ∀ ts,
      (ofTurns R.start h0 ts).IsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt (D.mid e.vtx e.edge) →
        (ofTurns R.start h0 ts).turning = W)
    (hphase : hexPhase_sideTilt head = -(5 / 8 : ℝ) * W) :
    HexFixedBoundaryPoint D heading where
  incidence := e
  head := head
  hHead := hHead
  mass := hexClosed_countObs R.inRegion R.start h0
    (D.mid e.vtx e.edge) hexChi
  mass_nonneg := tsum_nonneg (fun ts =>
    hexClosed_cw_nonneg R.inRegion R.start h0
      (D.mid e.vtx e.edge) hexChi_pos.le ts)
  phase := by
    rw [C.obs_eq,
      hexClosed_parafObservable_factor R.inRegion R.start h0
        (D.mid e.vtx e.edge) (5 / 8) hexChi W hdet]
    congr 2
    rw [hphase]
    push_cast
    ring


end StatMech.Universality
