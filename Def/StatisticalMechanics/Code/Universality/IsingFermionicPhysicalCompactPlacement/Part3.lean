/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part3


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def PhysicalEndpointLayerIncrementData.ofAnalyticOnCompactCenters
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (epsilon : Real) (hcollar : Metric.cthickening epsilon K ⊆ U)
    (hmesh_nonneg : forall k, 0 ≤ mesh k)
    (hmesh_collar : forall k, 2 * |mesh k| ≤ epsilon)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ K)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ K) :
    PhysicalEndpointLayerIncrementData N Phi mesh radius := by
  let K' := Metric.cthickening epsilon K
  let hex := exists_fderiv_im_norm_bound_on_compact
    Phi U K' hU hK.cthickening hcollar hPhi
  let L : NNReal := Classical.choose hex
  have hL : forall w, w ∈ K' ->
      ‖fderiv Real (fun z => (Phi z).im) w‖ ≤ L :=
    Classical.choose_spec hex
  have hsmooth : ContDiffOn Real 1 (fun z => (Phi z).im) U :=
    contDiffOn_im_of_analyticOnNhd 1 Phi U hPhi
  have hepsilon : 0 ≤ epsilon :=
    (mul_nonneg (by norm_num) (abs_nonneg (mesh 0))).trans
      (hmesh_collar 0)
  have hdifferentiable (w : Complex) (hw : w ∈ K') :
      DifferentiableAt Real (fun z => (Phi z).im) w :=
    (hsmooth.differentiableOn (by norm_num) w (hcollar hw)).differentiableAt
      (hU.mem_nhds (hcollar hw))
  refine
    { constant := 2 * L
      vertex := ?_
      face := ?_ }
  · intro k x hfixed hghost hendpoint y hxy
    let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
    let w := fullSquareScaledVertexEmbedding (N k) (mesh k) y
    have hz : z ∈ K := hvertex k x hfixed hghost hendpoint
    have hd : dist w z ≤ epsilon :=
      (fullSquareScaledVertexEmbedding_dist_le_two_abs
        (N k) (mesh k) x y hxy).trans (hmesh_collar k)
    have hball : Metric.closedBall z epsilon ⊆ K' :=
      Metric.closedBall_subset_cthickening hz epsilon
    have hdiff : ‖(Phi w).im - (Phi z).im‖ ≤
        (L : Real) * ‖w - z‖ :=
      (convex_closedBall z epsilon).norm_image_sub_le_of_norm_fderiv_le
        (fun q hq => hdifferentiable q (hball hq))
        (fun q hq => hL q (hball hq))
        (by simp [hepsilon]) (by simpa [Metric.mem_closedBall] using hd)
    change |(Phi w).im - (Phi z).im| ≤ (2 * L : NNReal) * mesh k
    rw [← Real.norm_eq_abs]
    calc
      ‖(Phi w).im - (Phi z).im‖ ≤ (L : Real) * ‖w - z‖ := hdiff
      _ = (L : Real) * dist w z := by rw [dist_eq_norm]
      _ ≤ (L : Real) * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledVertexEmbedding_dist_le_two_abs
          (N k) (mesh k) x y hxy
      _ = (2 * L : NNReal) * mesh k := by
        rw [abs_of_nonneg (hmesh_nonneg k)]
        norm_num
        ring
  · intro k c hfixed hghost hendpoint d hcd
    let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
    let w := fullSquareScaledFaceEmbedding (N k) (mesh k) d
    have hz : z ∈ K := hface k c hfixed hghost hendpoint
    have hd : dist w z ≤ epsilon :=
      (fullSquareScaledFaceEmbedding_dist_le_two_abs
        (N k) (mesh k) c d hcd).trans (hmesh_collar k)
    have hball : Metric.closedBall z epsilon ⊆ K' :=
      Metric.closedBall_subset_cthickening hz epsilon
    have hdiff : ‖(Phi w).im - (Phi z).im‖ ≤
        (L : Real) * ‖w - z‖ :=
      (convex_closedBall z epsilon).norm_image_sub_le_of_norm_fderiv_le
        (fun q hq => hdifferentiable q (hball hq))
        (fun q hq => hL q (hball hq))
        (by simp [hepsilon]) (by simpa [Metric.mem_closedBall] using hd)
    change |(Phi w).im - (Phi z).im| ≤ (2 * L : NNReal) * mesh k
    rw [← Real.norm_eq_abs]
    calc
      ‖(Phi w).im - (Phi z).im‖ ≤ (L : Real) * ‖w - z‖ := hdiff
      _ = (L : Real) * dist w z := by rw [dist_eq_norm]
      _ ≤ (L : Real) * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledFaceEmbedding_dist_le_two_abs
          (N k) (mesh k) c d hcd
      _ = (2 * L : NNReal) * mesh k := by
        rw [abs_of_nonneg (hmesh_nonneg k)]
        norm_num
        ring


def isingFermionicClosedUnitStrip : Set Complex :=
  {z | 0 ≤ z.im ∧ z.im ≤ 1}


def physicalFullSquareSampleCarrier
    (N : Nat -> Nat) (mesh : Nat -> Real) : Set Complex :=
  {z | (∃ k, ∃ x : FKIsingSquareFullVertexNode (N k),
      z = fullSquareScaledVertexEmbedding (N k) (mesh k) x) ∨
    (∃ k, ∃ c : FKIsingSquareFullFaceNode (N k),
      z = fullSquareScaledFaceEmbedding (N k) (mesh k) c)}


def physicalFullSquareLowerTraceCarrier
    (N : Nat -> Nat) (mesh : Nat -> Real) : Set Complex :=
  {z | (∃ k, ∃ x : FKIsingSquareFullVertexNode (N k),
      fkIsingSquareFullVertexFixedBoundary (N k) x ∧
        z = fullSquareScaledVertexEmbedding (N k) (mesh k) x) ∨
    (∃ k, ∃ c : FKIsingSquareFullFaceNode (N k),
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ∧
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ∧
        z = fullSquareScaledFaceEmbedding (N k) (mesh k) c)}


def physicalFullSquareUpperTraceCarrier
    (N : Nat -> Nat) (mesh : Nat -> Real) : Set Complex :=
  {z | (∃ k, ∃ c : FKIsingSquareFullFaceNode (N k),
      fkIsingSquareFullFaceFixedBoundary (N k) c ∧
        z = fullSquareScaledFaceEmbedding (N k) (mesh k) c) ∨
    (∃ k, ∃ x : FKIsingSquareFullVertexNode (N k),
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ∧
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ∧
        z = fullSquareScaledVertexEmbedding (N k) (mesh k) x)}


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
