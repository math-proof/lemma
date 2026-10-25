/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


structure HexFiniteStripBoundaryCore
    (R : HexFiniteRegion) (h0 : ℤ) (D : HexDomain V)
    (P : D.InteriorPairing) where
  sides : HexContourSides
  interior_sub : P.interior ⊆ D.incidences
  vertex_mem : ∀ v ∈ D.interiorVertices, D.pos v ∈ R.verts
  mid_mem : ∀ e ∈ D.incidences, D.mid e.vtx e.edge ∈ R.mids
  obs_eq : ∀ z, D.obs z =
    parafObservable R.inRegion R.start h0 z (5 / 8) hexChi
  lam : ℝ
  tau : ℝ
  ups : ℝ
  Fa : ℝ
  lam_eq : lam =
    hexContourLambda R.inRegion R.start h0 sides hexChi
  tau_eq : tau =
    hexContourTauPlus R.inRegion R.start h0 sides hexChi
      + hexContourTauMinus R.inRegion R.start h0 sides hexChi
  ups_eq : ups =
    hexContourUpsilon R.inRegion R.start h0 sides hexChi
  Fa_eq : (Fa : ℂ) = D.obs R.start

end StatMech.Universality
