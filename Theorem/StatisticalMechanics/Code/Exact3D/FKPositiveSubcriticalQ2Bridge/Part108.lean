/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part110
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem freeQ2DoubledEndpointDetourProb_le_boundary
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (hn : 1 ≤ n) :
    freeQ2DoubledEndpointDetourProb β hβpos n v ≤
      freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume
        β hβpos (2 * n) n := by
  unfold freeQ2DoubledEndpointDetourProb
    freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume
  exact measureReal_mono
    (boxConnectionDetourEvent_subset_boxBdryConnEvent_of_le
      3 hn (by omega : n ≤ 2 * n) v)


theorem freeQ2DoubledEndpointDetourProb_le_profile
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (hn : 1 ≤ n) :
    freeQ2DoubledEndpointDetourProb β hβpos n v ≤
      freeQ2BoundaryProfileOfBeta β hβpos n :=
  (freeQ2DoubledEndpointDetourProb_le_boundary β hβpos n v hn).trans
    (freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume_le_profile_of_le
      β hβpos (by omega : n ≤ 2 * n))


theorem boxConnEvent_subset_outerBoxConnEvent
    {d n M : ℕ} (h : n ≤ M) (x y : FK.boxVerts d n) :
    FK.boxConnEvent d n x y ⊆
      FK.boxConnEvent d M (FK.boxVertInclLE d h x) (FK.boxVertInclLE d h y) := by
  intro ω hω
  rw [FK.boxConnEvent, Set.mem_preimage, FK.mem_connEvent] at hω ⊢
  let f :
      (FK.openSub (FK.boxGraph d n) (FK.boxRestrict d n ω)) →g
        (FK.openSub (FK.boxGraph d M) (FK.boxRestrict d M ω)) :=
    { toFun := fun a => FK.boxVertInclLE d h a
      map_rel' := fun {a b} hab => by
        rw [FK.openSub_adj] at hab ⊢
        refine ⟨?_, ?_⟩
        · simpa [FK.boxGraph, FK.boxVertInclLE] using hab.1
        · change
            ω (FK.edgeIncl d M (FK.innerEdgeLE d h s(a, b))) = true
          rw [FK.edgeIncl_innerEdgeLE]
          exact hab.2 }
  exact hω.map f


theorem freeQ2DoubledInnerOriginConnProb_le_full
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n) :
    freeQ2DoubledInnerOriginConnProb β hβpos n v ≤
      freeQ2DoubledFullOriginConnProb β hβpos n v := by
  exact measureReal_mono
    (boxConnEvent_subset_outerBoxConnEvent
      (d := 3) (n := n) (M := 2 * n) (by omega : n ≤ 2 * n)
      (IsingFK.boxOrigin 3 n) v)


theorem freeQ2DoubledFullOriginConnProb_eq_inner_add_detour
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n) :
    freeQ2DoubledFullOriginConnProb β hβpos n v =
      freeQ2DoubledInnerOriginConnProb β hβpos n v +
        freeQ2DoubledEndpointDetourProb β hβpos n v := by
  let h : n ≤ 2 * n := by omega
  have horigin :
      FK.boxVertInclLE 3 h (IsingFK.boxOrigin 3 n) =
        IsingFK.boxOrigin 3 (2 * n) := by
    ext
    rfl
  simpa [freeQ2DoubledFullOriginConnProb, freeQ2DoubledInnerOriginConnProb,
    freeQ2DoubledEndpointDetourProb, h, horigin] using
    measureReal_full_boxConnEvent_eq_inner_add_detour
      (d := 3)
      (μ := (FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))))
      h (IsingFK.boxOrigin 3 n) v


theorem freeQ2DoubledInnerOriginConnProb_le_inner_add_error_of_full
    (β : ℝ) (hβpos : 0 < β) (n : ℕ)
    (v w : FK.boxVerts 3 n) (ε : ℝ)
    (hfull :
      freeQ2DoubledFullOriginConnProb β hβpos n v ≤
        freeQ2DoubledFullOriginConnProb β hβpos n w)
    (hdetour :
      freeQ2DoubledFullOriginConnProb β hβpos n w ≤
        freeQ2DoubledInnerOriginConnProb β hβpos n w + ε) :
    freeQ2DoubledInnerOriginConnProb β hβpos n v ≤
      freeQ2DoubledInnerOriginConnProb β hβpos n w + ε :=
  (freeQ2DoubledInnerOriginConnProb_le_full β hβpos n v).trans
    (hfull.trans hdetour)


theorem freeQ2DoubledInnerOriginConnProb_le_inner_add_detour_of_full
    (β : ℝ) (hβpos : 0 < β) (n : ℕ)
    (v w : FK.boxVerts 3 n)
    (hfull :
      freeQ2DoubledFullOriginConnProb β hβpos n v ≤
        freeQ2DoubledFullOriginConnProb β hβpos n w) :
    freeQ2DoubledInnerOriginConnProb β hβpos n v ≤
      freeQ2DoubledInnerOriginConnProb β hβpos n w +
        freeQ2DoubledEndpointDetourProb β hβpos n w :=
  freeQ2DoubledInnerOriginConnProb_le_inner_add_error_of_full
    β hβpos n v w (freeQ2DoubledEndpointDetourProb β hβpos n w)
    hfull
    (le_of_eq
      (freeQ2DoubledFullOriginConnProb_eq_inner_add_detour β hβpos n w))


end Exact3D
end StatMech
