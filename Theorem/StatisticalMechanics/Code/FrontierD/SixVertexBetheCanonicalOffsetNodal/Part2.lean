module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetBoundary
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffsetBound
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetNodalAbstract
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetRowContraction
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetNodalLimit
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetNodal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

theorem tendsto_sixVertexCanonicalOffsetNetMargin
    {c lower : Real} (hlower : 0 < lower) (r : Nat) :
    Tendsto (fun k => sixVertexCanonicalOffsetNetMargin c
      (sixVertexFourWidth r k) r lower) atTop
      (nhds (sixVertexFixedChargeOffsetContractionMargin c)) := by
  simpa [sixVertexCanonicalOffsetNetMargin] using
    tendsto_const_nhds.sub
      (tendsto_sixVertexFixedChargeOffsetRowError_of_lower hlower r)

theorem eventually_sixVertexCanonicalOffsetNetMargin_pos
    {c lower : Real} (hc : 2 < c) (hlower : 0 < lower) (r : Nat) :
    ∀ᶠ k : Nat in atTop,
      0 < sixVertexCanonicalOffsetNetMargin c
        (sixVertexFourWidth r k) r lower := by
  exact (tendsto_sixVertexCanonicalOffsetNetMargin hlower r).eventually
    (Ioi_mem_nhds (sixVertexFixedChargeOffsetContractionMargin_pos hc))

end
end StatMech.FrontierD
