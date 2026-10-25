/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlane.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.boundary_eq_lower_union_upper
    (E : PeriodicPlaneEmbedding P) (r s : ℝ) :
    E.rightHalfPlaneBoundaryVertices r =
      E.lowerBoundaryRayVertices r s ∪ E.upperBoundaryRayVertices r s := by
  ext x
  constructor
  · intro hx
    rcases le_total (E.vertexCoord x 1) s with hxs | hsx
    · exact Or.inl ⟨hx, hxs⟩
    · exact Or.inr ⟨hx, hsx⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx


theorem PeriodicPlaneEmbedding.rightHalfPlaneBoundary_coord_lt
    (E : PeriodicPlaneEmbedding P) {B r : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x : V} (hx : x ∈ E.rightHalfPlaneBoundaryVertices r) :
    E.vertexCoord x 0 < r + B := by
  obtain ⟨_hxr, y, hxy, hy⟩ := hx
  have hd := hB hxy (1 : unitInterval) (0 : Fin 2)
  have heq : E.coordinates (E.edgeArc hxy (1 : unitInterval) - E.vertex x) 0 =
      E.vertexCoord y 0 - E.vertexCoord x 0 := by
    rw [Path.target]
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  rw [heq] at hd
  have hd' := abs_le.mp hd
  linarith


theorem PeriodicPlaneEmbedding.lowerBoundaryRay_directional_sqrt_trick
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (r s : ℝ) (S : Set V)
    (hcomp : mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s)) ≤
      mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s))) :
    1 - Real.sqrt (1 - mu.real
        (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r))) ≤
      mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s)) := by
  let L := P.setConnectionWithin (E.rightHalfPlaneVertices r) S
    (E.lowerBoundaryRayVertices r s)
  let U := P.setConnectionWithin (E.rightHalfPlaneVertices r) S
    (E.upperBoundaryRayVertices r s)
  have hsqrt := directional_sqrt_trick mu hFKG
    (P.setConnectionWithin_isIncreasing (E.rightHalfPlaneVertices r) S
      (E.lowerBoundaryRayVertices r s))
    (P.setConnectionWithin_isIncreasing (E.rightHalfPlaneVertices r) S
      (E.upperBoundaryRayVertices r s))
    (P.setConnectionWithin_measurableSet (E.rightHalfPlaneVertices r) S
      (E.lowerBoundaryRayVertices r s))
    (P.setConnectionWithin_measurableSet (E.rightHalfPlaneVertices r) S
      (E.upperBoundaryRayVertices r s)) hcomp
  change 1 - Real.sqrt (1 - mu.real (L ∪ U)) ≤ mu.real L at hsqrt
  rw [← P.setConnectionWithin_union_target, ← E.boundary_eq_lower_union_upper]
    at hsqrt
  exact hsqrt


theorem PeriodicPlaneEmbedding.exists_shift_orbitBox_subset_rightHalfPlane
    (E : PeriodicPlaneEmbedding P) (N : ℕ) (r : ℝ) :
    ∃ z : Site 2, ∀ v ∈ P.orbitBox N,
      P.shift z v ∈ E.rightHalfPlaneVertices r := by
  classical
  let M : ℝ := ∑ v ∈ P.orbitBox N, |r - E.vertexCoord v 0|
  obtain ⟨n, hn⟩ := exists_nat_ge M
  let z : Site 2 := fun _ => (n : ℤ)
  refine ⟨z, ?_⟩
  intro v hv
  have hterm : |r - E.vertexCoord v 0| ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum
      (fun w _hw => abs_nonneg (r - E.vertexCoord w 0)) hv
  have hdiff : r - E.vertexCoord v 0 ≤ M :=
    (le_abs_self (r - E.vertexCoord v 0)).trans hterm
  change r ≤ E.vertexCoord (P.shift z v) 0
  rw [E.vertexCoord_shift]
  change r ≤ E.vertexCoord v 0 + (n : ℝ)
  linarith


theorem PeriodicPlaneEmbedding.exists_shift_connectedWithinOrbit_into_rightHalfPlane
    (E : PeriodicPlaneEmbedding P) (N : ℕ) (r : ℝ) :
    ∃ z : Site 2, ∀ (omega : ConfigSpace (Sym2 V)) (x y : V),
      omega ∈ P.connectedWithinOrbit x y N →
        P.configTranslate z omega ∈
          P.connectedWithinSet (E.rightHalfPlaneVertices r)
            (P.shift z x) (P.shift z y) := by
  obtain ⟨z, hz⟩ :=
    E.exists_shift_orbitBox_subset_rightHalfPlane (P.bufferedRadius N) r
  refine ⟨z, ?_⟩
  intro omega x y hxy
  have hsub : P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
      E.rightHalfPlaneVertices r := by
    rintro v ⟨u, hu, rfl⟩
    exact hz u hu
  apply P.connectedWithinSet_mono_region hsub (P.shift z x) (P.shift z y)
  apply (P.connectedWithinSet_configTranslate z omega
      (P.orbitBox (P.bufferedRadius N) : Set V) x y).2
  exact hxy


end StatMech.FK.PeriodicPlanar
