/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part7
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

theorem multibondCut_cubicalClosedSurfaceAnchoredEquiv
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (A : ClosedCubicalSurface a b c) :
    multibondCut cubicalDualEnds
        (cubicalClosedSurfaceAnchoredEquiv hb hc A).1 = A.1 := by
  change multibondCut cubicalDualEnds
      (cellFinsetAnchoredEquiv ((cubicalVolumeSurfaceEquiv hb hc).symm A)).1 = A.1
  rw [multibondCut_cellFinsetAnchored_eq_volumeBoundary ha hb hc]
  have h := congrArg Subtype.val
    ((cubicalVolumeSurfaceEquiv hb hc).apply_symm_apply A)
  exact h


theorem cubical_gaugePartition_isingDuality
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (K : CubicalPlaquette a b c → Real) (hK : ∀ p, 0 < K p) :
    (Real.exp (∑ p : CubicalPlaquette a b c,
        gaugeDualCoupling (K p)) * 2) *
        gaugePartition cubicalPlaquetteIncidence K =
      ((2 : Real) ^ Fintype.card (CubicalEdge a b c) *
        ∏ p : CubicalPlaquette a b c, Real.cosh (K p)) *
        multibondIsingPartition cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) := by
  apply gaugePartition_multibondIsingDuality
    cubicalPlaquetteIncidence K hK none cubicalDualEnds
    (cubicalClosedSurfaceAnchoredEquiv hb hc)
  exact multibondCut_cubicalClosedSurfaceAnchoredEquiv ha hb hc


theorem cubicalXYWilsonExpectation_eq_typedDisorderRatio
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c → Real)
    (hK : ∀ p, 0 < K p) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) =
      (∑ s : AnchoredConfig (CubicalDualVertex a b c) none,
          ∏ p ∈ multibondCut cubicalDualEnds s.1 ∆ cubicalXYSheet k,
            Real.exp (-2 * gaugeDualCoupling (K p))) /
        (∑ s : AnchoredConfig (CubicalDualVertex a b c) none,
          ∏ p ∈ multibondCut cubicalDualEnds s.1,
            Real.exp (-2 * gaugeDualCoupling (K p))) := by
  apply gaugeWilsonExpectation_eq_multibondDisorderRatio_of_sheet
    cubicalPlaquetteIncidence K hK (cubicalXYLoop k) (cubicalXYSheet k)
    (cubicalXYSheet_hasWilsonBoundary k) none cubicalDualEnds
    (cubicalClosedSurfaceAnchoredEquiv hb hc)
  exact multibondCut_cubicalClosedSurfaceAnchoredEquiv ha hb hc

end
end StatMech.FrontierA
