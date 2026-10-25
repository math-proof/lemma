/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part4
import Structure.StatisticalMechanics.Code.Universality.HexStartPhaseRepair


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexFiniteStripBoundaryCore

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing}


def ofBoundaryData (B : HexFiniteStripBoundaryData R h0 D P) :
    HexFiniteStripBoundaryCore R h0 D P where
  sides := B.sides
  interior_sub := B.interior_sub
  vertex_mem := B.vertex_mem
  mid_mem := B.mid_mem
  obs_eq := B.obs_eq
  lam := B.lam
  tau := B.tau
  ups := B.ups
  Fa := B.Fa
  lam_eq := B.lam_eq
  tau_eq := B.tau_eq
  ups_eq := B.ups_eq
  Fa_eq := B.Fa_eq


end HexFiniteStripBoundaryCore
end StatMech.Universality
