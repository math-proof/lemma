/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexContourDefs.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripBoundary.Part2


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexFiniteStripBoundaryData

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing} (B : HexFiniteStripBoundaryData R h0 D P)


theorem boundary_identity (hFa : B.Fa = 1) :
    hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = 1 :=
  B.toFObsBoundaryData.boundaryIdentity hFa


theorem contour_boundary_identity (hFa : B.Fa = 1) :
    hexBdryCl * hexContourLambda R.inRegion R.start h0 B.sides hexChi
      + hexBdryCt *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi)
      + hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
  rw [← B.lam_eq, ← B.tau_eq, ← B.ups_eq]
  exact B.boundary_identity hFa

end HexFiniteStripBoundaryData


theorem hexFiniteStrip_boundary_identity_scales
    (R : ℕ → HexFiniteRegion) (h0 : ℕ → ℤ)
    (D : ℕ → HexDomain V) (P : ∀ v, (D v).InteriorPairing)
    (B : ∀ v, HexFiniteStripBoundaryData (R v) (h0 v) (D v) (P v))
    (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (B v).lam + hexBdryCt * (B v).tau + (B v).ups = 1 := by
  intro v hv
  exact (B v).boundary_identity (hFa v hv)

end StatMech.Universality
