/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part2


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem fullSquareScaledVertexEmbedding_east
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .east) :
    fullSquareScaledVertexEmbedding n scale
        (fkIsingSquareNeighbor n x .east h) =
      fullSquareScaledVertexEmbedding n scale x +
        (scale : Complex) * (1 + Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledVertexEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, Matrix.vecHead, Matrix.vecTail] <;>
    ring

theorem fullSquareScaledVertexEmbedding_north
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .north) :
    fullSquareScaledVertexEmbedding n scale
        (fkIsingSquareNeighbor n x .north h) =
      fullSquareScaledVertexEmbedding n scale x +
        (scale : Complex) * (1 - Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledVertexEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, Matrix.vecHead, Matrix.vecTail] <;>
    ring

theorem fullSquareScaledVertexEmbedding_west
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .west) :
    fullSquareScaledVertexEmbedding n scale
        (fkIsingSquareNeighbor n x .west h) =
      fullSquareScaledVertexEmbedding n scale x -
        (scale : Complex) * (1 + Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledVertexEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, Matrix.vecHead, Matrix.vecTail] <;>
    ring

theorem fullSquareScaledVertexEmbedding_south
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .south) :
    fullSquareScaledVertexEmbedding n scale
        (fkIsingSquareNeighbor n x .south h) =
      fullSquareScaledVertexEmbedding n scale x -
        (scale : Complex) * (1 - Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledVertexEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, Matrix.vecHead, Matrix.vecTail] <;>
    ring

theorem fullSquareScaledFaceEmbedding_east
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (h : c.1.1 + 1 < 2 * n) :
    fullSquareScaledFaceEmbedding n scale (faceEastNeighbor n c h) =
      fullSquareScaledFaceEmbedding n scale c +
        (scale : Complex) * (1 + Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledFaceEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      faceEastNeighbor] <;>
    ring

theorem fullSquareScaledFaceEmbedding_north
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (h : c.2.1 + 1 < 2 * n) :
    fullSquareScaledFaceEmbedding n scale (faceNorthNeighbor n c h) =
      fullSquareScaledFaceEmbedding n scale c +
        (scale : Complex) * (1 - Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledFaceEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      faceNorthNeighbor] <;>
    ring

theorem fullSquareScaledFaceEmbedding_west
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (h : 0 < c.1.1) :
    fullSquareScaledFaceEmbedding n scale (faceWestNeighbor n c h) =
      fullSquareScaledFaceEmbedding n scale c -
        (scale : Complex) * (1 + Complex.I) := by
  have hc : 1 ≤ c.1.1 := h
  apply Complex.ext <;>
    simp [fullSquareScaledFaceEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      faceWestNeighbor, Nat.cast_sub hc] <;>
    ring

theorem fullSquareScaledFaceEmbedding_south
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (h : 0 < c.2.1) :
    fullSquareScaledFaceEmbedding n scale (faceSouthNeighbor n c h) =
      fullSquareScaledFaceEmbedding n scale c -
        (scale : Complex) * (1 - Complex.I) := by
  have hc : 1 ≤ c.2.1 := h
  apply Complex.ext <;>
    simp [fullSquareScaledFaceEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      faceSouthNeighbor, Nat.cast_sub hc] <;>
    ring

theorem fullSquareScaledVertex_sampledLaplacian_eq_stencil
    (n : Nat) (scale : Real) (f : Complex → Real)
    (x : FKIsingSquareFullVertexNode n)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y ↦ f (fullSquareScaledVertexEmbedding n scale y)) x =
      complexDirectionalFourNeighborStencil f
        (fullSquareScaledVertexEmbedding n scale x)
        (1 + Complex.I) (1 - Complex.I) scale := by
  let xE := fkIsingSquareNeighbor n x .east heast
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let xS := fkIsingSquareNeighbor n x .south hsouth
  have hEN : xE ≠ xN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 0) h
    simp [xE, xN, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hEW : xE ≠ xW := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 0) h
    simp [xE, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hES : xE ≠ xS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 0) h
    simp [xE, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hNW : xN ≠ xW := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 1) h
    simp [xN, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hNS : xN ≠ xS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 1) h
    simp [xN, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hWS : xW ≠ xS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 0) h
    simp [xW, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  unfold isingFiniteGraphLaplacian fkIsingSquareFullVertexGraph
  rw [fkIsingSquareFullVertex_neighborFinset n x heast hnorth hwest hsouth]
  simp [xE, xN, xW, xS, hEN, hEW, hES, hNW, hNS, hWS]
  unfold complexDirectionalFourNeighborStencil
  rw [fullSquareScaledVertexEmbedding_east,
    fullSquareScaledVertexEmbedding_north,
    fullSquareScaledVertexEmbedding_west,
    fullSquareScaledVertexEmbedding_south]
  ring

theorem fullSquareScaledFace_sampledLaplacian_eq_stencil
    (n : Nat) (scale : Real) (f : Complex → Real)
    (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d ↦ f (fullSquareScaledFaceEmbedding n scale d)) c =
      complexDirectionalFourNeighborStencil f
        (fullSquareScaledFaceEmbedding n scale c)
        (1 + Complex.I) (1 - Complex.I) scale := by
  classical
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cW := faceWestNeighbor n c hwest
  let cS := faceSouthNeighbor n c hsouth
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hEW : cE ≠ cW := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cW, faceEastNeighbor, faceWestNeighbor] at h0
    omega
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNW : cN ≠ cW := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
    simp [cN, cW, faceNorthNeighbor, faceWestNeighbor] at h1
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  have hWS : cW ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cW, cS, faceWestNeighbor, faceSouthNeighbor] at h0
    omega
  unfold isingFiniteGraphLaplacian
  rw [fkIsingSquareBoundaryFullFace_neighborFinset
    n c heast hnorth hwest hsouth]
  change ∑ d ∈ {cE, cN, cW, cS},
    (f (fullSquareScaledFaceEmbedding n scale d) -
      f (fullSquareScaledFaceEmbedding n scale c)) = _
  simp [hEN, hEW, hES, hNW, hNS, hWS]
  unfold complexDirectionalFourNeighborStencil
  rw [fullSquareScaledFaceEmbedding_east,
    fullSquareScaledFaceEmbedding_north,
    fullSquareScaledFaceEmbedding_west,
    fullSquareScaledFaceEmbedding_south]
  ring

theorem fullSquareScaledVertex_sampledLaplacian_le_fourthOrder
    (n : Nat) (scale : Real) (f : Complex → Real)
    (x : FKIsingSquareFullVertexNode n)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (M₁ M₂ : Real)
    (hg₁ : ContDiff Real 4 (fun t : Real ↦ f
      (fullSquareScaledVertexEmbedding n scale x +
        (t : Complex) * (1 + Complex.I))))
    (hg₂ : ContDiff Real 4 (fun t : Real ↦ f
      (fullSquareScaledVertexEmbedding n scale x +
        (t : Complex) * (1 - Complex.I))))
    (hfourth₁ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f
      (fullSquareScaledVertexEmbedding n scale x +
        (s : Complex) * (1 + Complex.I))) t| ≤ M₁)
    (hfourth₂ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f
      (fullSquareScaledVertexEmbedding n scale x +
        (s : Complex) * (1 - Complex.I))) t| ≤ M₂)
    (hharmonic : iteratedDeriv 2 (fun t : Real ↦ f
        (fullSquareScaledVertexEmbedding n scale x +
          (t : Complex) * (1 + Complex.I))) 0 +
      iteratedDeriv 2 (fun t : Real ↦ f
        (fullSquareScaledVertexEmbedding n scale x +
          (t : Complex) * (1 - Complex.I))) 0 = 0) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y ↦ f (fullSquareScaledVertexEmbedding n scale y)) x| ≤
        (M₁ + M₂) * |scale| ^ 4 / 12 := by
  rw [fullSquareScaledVertex_sampledLaplacian_eq_stencil
    n scale f x heast hnorth hwest hsouth]
  exact complexDirectionalFourNeighborStencil_le f
    (fullSquareScaledVertexEmbedding n scale x)
    (1 + Complex.I) (1 - Complex.I) scale M₁ M₂
    hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

theorem fullSquareScaledFace_sampledLaplacian_le_fourthOrder
    (n : Nat) (scale : Real) (f : Complex → Real)
    (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1)
    (M₁ M₂ : Real)
    (hg₁ : ContDiff Real 4 (fun t : Real ↦ f
      (fullSquareScaledFaceEmbedding n scale c +
        (t : Complex) * (1 + Complex.I))))
    (hg₂ : ContDiff Real 4 (fun t : Real ↦ f
      (fullSquareScaledFaceEmbedding n scale c +
        (t : Complex) * (1 - Complex.I))))
    (hfourth₁ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f
      (fullSquareScaledFaceEmbedding n scale c +
        (s : Complex) * (1 + Complex.I))) t| ≤ M₁)
    (hfourth₂ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f
      (fullSquareScaledFaceEmbedding n scale c +
        (s : Complex) * (1 - Complex.I))) t| ≤ M₂)
    (hharmonic : iteratedDeriv 2 (fun t : Real ↦ f
        (fullSquareScaledFaceEmbedding n scale c +
          (t : Complex) * (1 + Complex.I))) 0 +
      iteratedDeriv 2 (fun t : Real ↦ f
        (fullSquareScaledFaceEmbedding n scale c +
          (t : Complex) * (1 - Complex.I))) 0 = 0) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun d ↦ f (fullSquareScaledFaceEmbedding n scale d)) c| ≤
        (M₁ + M₂) * |scale| ^ 4 / 12 := by
  rw [fullSquareScaledFace_sampledLaplacian_eq_stencil
    n scale f c heast hnorth hwest hsouth]
  exact complexDirectionalFourNeighborStencil_le f
    (fullSquareScaledFaceEmbedding n scale c)
    (1 + Complex.I) (1 - Complex.I) scale M₁ M₂
    hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

theorem fullSquareScaledCoordinateEmbedding_unitAxial_dist
    (scale : Real) (hscale : 0 ≤ scale) (u v : Int × Int)
    (hunit : v = (u.1 + 1, u.2) ∨
      v = (u.1, u.2 + 1) ∨
      v = (u.1 - 1, u.2) ∨
      v = (u.1, u.2 - 1)) :
    dist (fullSquareScaledCoordinateEmbedding scale v)
      (fullSquareScaledCoordinateEmbedding scale u) ≤ scale := by
  rcases hunit with rfl | rfl | rfl | rfl <;>
    simp only [fullSquareScaledCoordinateEmbedding] <;>
    rw [dist_smul₀] <;>
    simp [fkIsingSquareWiredIntPoint, Complex.dist_eq_re_im,
      abs_of_nonneg hscale]


theorem FullSquareCoordinateEmbeddingCompatibility.incidenceDistance
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex}
    {faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex}
    {mesh : Nat → Real}
    (C : FullSquareCoordinateEmbeddingCompatibility
      N vertexEmbedding faceEmbedding mesh) (k : Nat)
    (e : FKIsingSquareInteriorRadialIncidence (N k) (hN k)) :
    dist
        (faceEmbedding k
          (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))
        (vertexEmbedding k
          (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) ≤ mesh k := by
  rw [C.face_eq_coordinate, C.vertex_eq_coordinate]
  exact C.unitAxial_dist_le_mesh k _ _
    (fkIsingSquareFull_radiallyAdjacent_of_incidence (N k) (hN k) e)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
