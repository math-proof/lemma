/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part6


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredBoundaryVertexSquareRepresentative_normSq
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    Complex.normSq
        (fkIsingSquareWiredBoundaryVertexSquareRepresentative n hn side k) =
      isingFermionicBoundaryVertexNormSqFactor *
        Complex.normSq
          (fkIsingSquareWiredBoundaryMedialObservable n hn side k) := by
  rw [fkIsingSquareWiredBoundaryVertexSquareRepresentative,
    Complex.normSq_mul]
  have hfactor : 0 <= isingFermionicBoundaryVertexNormSqFactor :=
    isingFermionicBoundaryVertexNormSqFactor_pos.le
  simp [Complex.normSq_ofReal, Real.mul_self_sqrt hfactor]


theorem fkIsingSquareWiredBoundaryVertexSquareRepresentative_halfDiagonal_normSq
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareWiredBoundaryVertexSquareRepresentative n hn side k) =
      isingFermionicGhostCoefficient *
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterRetainedSide side)) := by
  rw [fkIsingSquareWiredBoundaryVertexSquareRepresentative_normSq]
  rw [← mul_assoc,
    isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor]
  rfl


theorem fkIsingSquareWiredBoundaryMedialObservable_square
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    fkIsingSquareBoundaryTangent side *
        fkIsingSquareWiredBoundaryMedialObservable n hn side k ^ 2 =
      (fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterRetainedSide side)) : Complex) := by
  unfold fkIsingSquareWiredBoundaryMedialObservable
  rw [← fkIsingSquarePerimeterRetained_tangent n hn side k]
  exact fkIsingSquareWired_tangent_mul_observable_sq_eq_increment n hn _


theorem fkIsingSquareWiredBoundaryVertexSquareRepresentative_square
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    fkIsingSquareBoundaryTangent side *
        fkIsingSquareWiredBoundaryVertexSquareRepresentative n hn side k ^ 2 =
      (isingFermionicBoundaryVertexNormSqFactor *
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterRetainedSide side)) : Real) := by
  rw [fkIsingSquareWiredBoundaryVertexSquareRepresentative]
  have hfactor : 0 <= isingFermionicBoundaryVertexNormSqFactor :=
    isingFermionicBoundaryVertexNormSqFactor_pos.le
  have hsqrt := Real.sq_sqrt hfactor
  calc
    _ = (isingFermionicBoundaryVertexNormSqFactor : Complex) *
          (fkIsingSquareBoundaryTangent side *
            fkIsingSquareWiredBoundaryMedialObservable n hn side k ^ 2) := by
      rw [mul_pow]
      rw [show (Real.sqrt isingFermionicBoundaryVertexNormSqFactor :
          Complex) ^ 2 = isingFermionicBoundaryVertexNormSqFactor by
        exact_mod_cast hsqrt]
      ring
    _ = _ := by
      rw [fkIsingSquareWiredBoundaryMedialObservable_square]
      norm_cast


theorem fkIsingSquareWiredBoundaryMedialObservable_exists_nonnegative_square
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    ∃ t : Real, 0 ≤ t ∧
      fkIsingSquareBoundaryTangent side *
          fkIsingSquareWiredBoundaryMedialObservable n hn side k ^ 2 =
        (t : Complex) := by
  refine ⟨fkIsingSquareWiredPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterRetainedSide side)),
    fkIsingSquareWiredPrimitiveIncrement_nonneg n hn _, ?_⟩
  exact fkIsingSquareWiredBoundaryMedialObservable_square n hn side k


theorem fkIsingSquareWiredPerimeterInterior_face_sub_vertex
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
          (fkIsingSquareFullFaceOfRadialIncidence n hn
            (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareBoundaryVertex n (side, k)) =
      fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterInteriorSide side)) := by
  let e := fkIsingSquarePerimeterInteriorRadialIncidence n hn side k
  have h := FKIsingSquareFullIntegratedPrimitive.face_sub_vertex n hn e
  rw [fkIsingSquarePerimeterInteriorRadialEndpoint n hn side k] at h
  simpa only [e, fkIsingSquarePerimeterInteriorRadialIncidence,
    fkIsingSquareInteriorRadialIncrement_mk,
    fkIsingSquarePerimeterInteriorRadialDart] using h


theorem fkIsingSquareWiredPerimeterInterior_vertex_le_face
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
        (fkIsingSquareBoundaryVertex n (side, k)) ≤
      FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
        (fkIsingSquareFullFaceOfRadialIncidence n hn
          (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) := by
  let e := fkIsingSquarePerimeterInteriorRadialIncidence n hn side k
  have h := FKIsingSquareFullIntegratedPrimitive.vertex_le_face n hn e
  rw [fkIsingSquarePerimeterInteriorRadialEndpoint n hn side k] at h
  exact h


theorem fkIsingSquareWiredPerimeterInterior_face_sub_vertex_nonneg
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    0 ≤ FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
          (fkIsingSquareFullFaceOfRadialIncidence n hn
            (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareBoundaryVertex n (side, k)) := by
  rw [fkIsingSquareWiredPerimeterInterior_face_sub_vertex n hn side k]
  exact fkIsingSquareWiredPrimitiveIncrement_nonneg n hn _

namespace FKIsingSquareFullIntegratedPrimitive


theorem vertex_modifiedLaplacian_nonpos_of_interior
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (vertexPrimitive n hn) x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - vertexPrimitive n hn x) <= 0 := by
  have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 0 := by
    unfold fkIsingSquareFullVertexGhostMultiplicity
    simp [fkIsingSquareDirectionAvailable] at heast hnorth hwest hsouth
    split_ifs <;> omega
  rw [show fkIsingSquareFullVertexGraph n = (fkSquareBoxPlanar n).G from rfl]
  simp [isingFermionicGhostRate, hmult]
  exact vertex_laplacian_nonpos_of_interior n hn x
    heast hnorth hwest hsouth


theorem face_modifiedLaplacian_nonneg_of_interior
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1) :
    0 <= isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (facePrimitive n hn) c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (0 - facePrimitive n hn c) := by
  have hmult : fkIsingSquareFullFaceGhostMultiplicity n c = 0 := by
    unfold fkIsingSquareFullFaceGhostMultiplicity
    split_ifs <;> omega
  simp [isingFermionicGhostRate, hmult]
  exact face_laplacian_nonneg_of_interior n hn c
    heast hnorth hwest hsouth

end FKIsingSquareFullIntegratedPrimitive

theorem fkIsingSquareWiredFullMedialObservable_eq_retained_of_cancellation
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n))
    (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
    fkIsingSquareWiredFullMedialObservable n hn
        (fkIsingSquarePerimeterEdge n side k) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterRetainedSide side)) := by
  rcases h with ⟨-, hzero⟩
  cases side <;>
    simp only [fkIsingSquarePerimeterCancelledSide] at hzero <;>
    simp [fkIsingSquareWiredFullMedialObservable,
      fkIsingSquarePerimeterRetainedSide, hzero]

theorem fkIsingSquareWiredFullMedialObservable_boundary_square
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n))
    (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
    fkIsingSquareBoundaryTangent side *
        fkIsingSquareWiredFullMedialObservable n hn
          (fkIsingSquarePerimeterEdge n side k) ^ 2 =
      (fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterRetainedSide side)) : Complex) := by
  rw [fkIsingSquareWiredFullMedialObservable_eq_retained_of_cancellation
    n hn side k h]
  rw [← fkIsingSquarePerimeterRetained_tangent n hn side k]
  exact fkIsingSquareWired_tangent_mul_observable_sq_eq_increment n hn _

theorem fkIsingSquareWiredFullMedialObservable_exists_nonnegative_boundary_square
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n))
    (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
    ∃ t : Real, 0 ≤ t ∧
      fkIsingSquareBoundaryTangent side *
          fkIsingSquareWiredFullMedialObservable n hn
            (fkIsingSquarePerimeterEdge n side k) ^ 2 = (t : Complex) := by
  refine ⟨fkIsingSquareWiredPrimitiveIncrement n hn
      (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterRetainedSide side)),
    fkIsingSquareWiredPrimitiveIncrement_nonneg n hn _, ?_⟩
  exact fkIsingSquareWiredFullMedialObservable_boundary_square n hn side k h

theorem normSq_proj_I_eq_negI_of_proj_neg_one_eq_zero
    (F : Complex) (h : isingProj (-1) F = 0) :
    Complex.normSq (isingProj Complex.I F) =
      Complex.normSq (isingProj (-Complex.I) F) := by
  have hi := congrArg Complex.im h
  simp [isingProj] at hi
  simp [isingProj, Complex.normSq_apply]
  ring_nf at hi ⊢
  rw [hi]
  ring

theorem normSq_proj_I_eq_negI_of_proj_one_eq_zero
    (F : Complex) (h : isingProj 1 F = 0) :
    Complex.normSq (isingProj Complex.I F) =
      Complex.normSq (isingProj (-Complex.I) F) := by
  have hr := congrArg Complex.re h
  simp [isingProj] at hr
  simp [isingProj, Complex.normSq_apply]
  ring_nf at hr ⊢
  rw [hr]
  ring

theorem normSq_proj_one_eq_neg_one_of_proj_negI_eq_zero
    (F : Complex) (h : isingProj (-Complex.I) F = 0) :
    Complex.normSq (isingProj 1 F) =
      Complex.normSq (isingProj (-1) F) := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [isingProj] at hr hi
  simp [isingProj, Complex.normSq_apply]
  ring_nf at hr hi ⊢
  rw [show F.re = -F.im by linarith]
  ring

theorem normSq_proj_one_eq_neg_one_of_proj_I_eq_zero
    (F : Complex) (h : isingProj Complex.I F = 0) :
    Complex.normSq (isingProj 1 F) =
      Complex.normSq (isingProj (-1) F) := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [isingProj] at hr hi
  simp [isingProj, Complex.normSq_apply]
  ring_nf at hr hi ⊢
  rw [show F.re = F.im by linarith]


theorem fkIsingSquareWiredPerimeter_south_increment_eq_north_of_cancellation
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n))
    (h : FKIsingSquarePerimeterCancellationAt n hn side k) :
    fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k, .south)) =
      fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k, .north)) := by
  let e := fkIsingSquarePerimeterEdge n side k
  let F := fkIsingSquareWiredFullMedialObservable n hn e
  have hzero := h.2
  have hproj : isingProj
      (fkIsingSquareWiredDirectedTangent n hn
        (.dart (e, fkIsingSquarePerimeterCancelledSide side))) F = 0 := by
    rw [fkIsingSquareWiredFullMedialObservable_projection]
    exact hzero
  rw [fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection,
    fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection]
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨-, hE, hS, hN⟩
      rw [hS, hN]
      apply normSq_proj_I_eq_negI_of_proj_neg_one_eq_zero F
      simpa [fkIsingSquarePerimeterCancelledSide, hE] using hproj
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨hW, -, hS, hN⟩
      rw [hS, hN]
      apply normSq_proj_one_eq_neg_one_of_proj_negI_eq_zero F
      simpa [fkIsingSquarePerimeterCancelledSide, hW] using hproj
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨hW, -, hS, hN⟩
      rw [hS, hN]
      apply normSq_proj_I_eq_negI_of_proj_one_eq_zero F
      simpa [fkIsingSquarePerimeterCancelledSide, hW] using hproj
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨-, hE, hS, hN⟩
      rw [hS, hN]
      apply normSq_proj_one_eq_neg_one_of_proj_I_eq_zero F
      simpa [fkIsingSquarePerimeterCancelledSide, hE] using hproj

end
end StatMech.Universality
