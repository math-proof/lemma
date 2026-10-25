/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexBalanced_iteratedLimit_iff_widthRate
    {c a : ℝ} (hc : 0 < c) :
    SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c) a ↔
      Tendsto (sixVertexCentralWidthRate c) atTop (nhds a) := by
  constructor
  · rintro ⟨g, hg, hga⟩
    have heq : g = sixVertexCentralWidthRate c := by
      funext k
      exact tendsto_nhds_unique (hg k)
        (sixVertexBalancedAreaDensity_tendsto_widthRate hc k)
    simpa [heq] using hga
  · intro h
    exact ⟨sixVertexCentralWidthRate c,
      sixVertexBalancedAreaDensity_tendsto_widthRate hc, h⟩


theorem sixVertexAntiferroelectricFreeEnergyFormula_iff_widthBethe
    {c lam : ℝ} (hc : 0 < c) :
    SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c)
        (sixVertexAntiferroelectricFreeEnergyValue lam) ↔
      Tendsto (sixVertexCentralWidthRate c) atTop
        (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) := by
  exact sixVertexBalanced_iteratedLimit_iff_widthRate hc

end StatMech.FrontierD
