/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part13


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexCSA (T L : ℕ) (hT : 0 < T) : ℝ :=
  ∑ i : HexCSPairIndex T L,
    if hexCSBoundaryClass i.1 = .side then
      2 * endpointCountObservable
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWMid i.1.vtx.1 i.1.edge) hexChi
    else 0


noncomputable def hexCSE (T L : ℕ) (hT : 0 < T) : ℝ :=
  ∑ i : HexCSPairIndex T L,
    if hexCSBoundaryClass i.1 = .slant then
      2 * endpointCountObservable
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWMid i.1.vtx.1 i.1.edge) hexChi
    else 0


noncomputable def hexCSB (T L : ℕ) (hT : 0 < T) : ℝ :=
  (∑ i : HexCSPairIndex T L,
      if hexCSBoundaryClass i.1 = .top then
        2 * endpointCountObservable
          (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
          (hexAWMid i.1.vtx.1 i.1.edge) hexChi
      else 0) +
    ∑ k : HexCSFixedIndex T L hT,
      endpointCountObservable
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWMid k.1.vtx.1 k.1.edge) hexChi

end
end StatMech.Universality
