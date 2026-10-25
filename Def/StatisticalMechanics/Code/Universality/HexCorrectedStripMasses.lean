/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMasses.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexCSIncidenceMass
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass)
    (e : HexCSIncidence T L) : ℝ :=
  if hexCSBoundaryClass e = cls then
    endpointCountObservable (hexCSFiniteRegion T L hT).inRegion
      hexAWStart 1 (hexAWMid e.vtx.1 e.edge) hexChi
  else 0


noncomputable def hexCSLiteralBoundaryMass
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) : ℝ :=
  ∑ e ∈ hexCSBoundaryIncidences T L \ {hexCSStartIncidence T L hT},
    hexCSIncidenceMass T L hT cls e

end
end StatMech.Universality
