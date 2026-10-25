/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


structure HexFixedBoundaryPoint
    {V : Type*} [DecidableEq V]
    (D : HexDomain V) (heading : V → Fin 3 → ℤ) where
  incidence : HexIncidence V
  head : ℤ
  hHead : heading incidence.vtx incidence.edge = head
  mass : ℝ
  mass_nonneg : 0 ≤ mass
  phase : D.obs (D.mid incidence.vtx incidence.edge) =
    Complex.exp ((hexPhase_sideTilt head : ℝ) * Complex.I) * (mass : ℂ)

end StatMech.Universality
