/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


noncomputable def hexMirrorBoundaryPair_of_reflection
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P)
    (heading : V → Fin 3 → ℤ)
    (eNeg ePos : HexIncidence V)
    (hne : eNeg ≠ ePos)
    (headNeg headPos : ℤ)
    (hHeadNeg : heading eNeg.vtx eNeg.edge = headNeg)
    (hHeadPos : heading ePos.vtx ePos.edge = headPos)
    (hmidPos : D.mid ePos.vtx ePos.edge =
      hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
    (hsym : ∀ m, R.inRegion m →
      R.inRegion (hsc_refl R.start h0 m))
    (W : ℝ)
    (hdetNeg : ∀ ts,
      (ofTurns R.start h0 ts).IsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt
            (D.mid eNeg.vtx eNeg.edge) →
        (ofTurns R.start h0 ts).turning = W)
    (htilt : hexPhase_sideTilt headPos =
      -hexPhase_sideTilt headNeg) :
    HexMirrorBoundaryPair D heading where
  neg := {eNeg}
  pos := {ePos}
  disjoint := by
    simp [hne]
  headNeg := headNeg
  headPos := headPos
  hHeadNeg := by
    intro e he
    simpa only [Finset.mem_singleton.mp he] using hHeadNeg
  hHeadPos := by
    intro e he
    simpa only [Finset.mem_singleton.mp he] using hHeadPos
  angle := hexPhase_sideTilt headNeg + (5 / 8 : ℝ) * W
  mass := hexClosed_countObs R.inRegion R.start h0
    (D.mid eNeg.vtx eNeg.edge) hexChi
  phaseNeg := by
    rw [Finset.sum_singleton, C.obs_eq,
      hexClosed_parafObservable_factor R.inRegion R.start h0
        (D.mid eNeg.vtx eNeg.edge) (5 / 8) hexChi W hdetNeg]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  phasePos := by
    have hdetPos := hsc_detb_of_dett R.inRegion R.start h0
      (D.mid eNeg.vtx eNeg.edge) W hsym hdetNeg
    rw [Finset.sum_singleton, C.obs_eq, hmidPos,
      hexClosed_parafObservable_factor R.inRegion R.start h0
        (hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
        (5 / 8) hexChi (-W) hdetPos,
      hsc_countObs_refl R.inRegion R.start h0
        (D.mid eNeg.vtx eNeg.edge) hexChi hsym]
    rw [← mul_assoc, ← Complex.exp_add, htilt]
    congr 2
    push_cast
    ring

end StatMech.Universality
