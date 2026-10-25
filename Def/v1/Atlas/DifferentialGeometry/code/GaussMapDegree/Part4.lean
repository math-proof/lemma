/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Hausdorff
import Structure.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part3


noncomputable section

open scoped Matrix

namespace GaussMapDegree

def sphereVolume (n : ℕ) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure (↑n : ℝ)
    {x : Fin (n + 1) → ℝ | ‖x‖ = 1}).toReal

def jacobianDetAtPoint {n : ℕ} (φ : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (σ : (Fin n → ℝ) → Fin (n + 1) → ℝ) (u : Fin n → ℝ)
    (ν_tilde : Fin (n + 1) → ℝ) : ℝ :=
  let Dφσ : Matrix (Fin (n + 1)) (Fin n) ℝ :=
    fun i j => fderiv ℝ (φ ∘ σ) u (Function.update 0 j 1) i
  (augmentedMatrix Dφσ ν_tilde).det / Real.sqrt ((gramMatrix n σ u).det)

def SmoothMapBetweenHypersurfaces.tangentMapDet {n : ℕ}
    (f : SmoothMapBetweenHypersurfaces n)
    (p : Fin (n + 1) → ℝ) : ℝ :=

  let ν_tilde := Classical.choose f.M_tilde_oriented

  let chartData := Classical.epsilon (fun (data : (Fin n → ℝ) × ((Fin n → ℝ) → Fin (n + 1) → ℝ)) =>
    let u := data.1
    let σ := data.2
    σ u = p)
  let u := chartData.1
  let σ := chartData.2
  jacobianDetAtPoint f.φ σ u (ν_tilde (f.φ p))

def degreeOfMapBetweenHypersurfacesReal {n : ℕ}
    (f : SmoothMapBetweenHypersurfaces n) : ℝ :=
  let μ := MeasureTheory.Measure.hausdorffMeasure (↑n : ℝ)
  (1 / hypersurfaceVolume n f.M_tilde) *
    ∫ p in f.M, f.tangentMapDet p ∂μ

def degreeOfMapBetweenHypersurfaces {n : ℕ}
    (f : SmoothMapBetweenHypersurfaces n) : ℤ :=
  ⌊degreeOfMapBetweenHypersurfacesReal f + 1 / 2⌋

def SmoothMapToSphere.toSmoothMapBetweenHypersurfaces {n : ℕ}
    (f : SmoothMapToSphere n)
    (sphere_hypersurface : IsSmHypersurface n {x : Fin (n + 1) → ℝ | ‖x‖ = 1})
    (sphere_connected : IsConnected {x : Fin (n + 1) → ℝ | ‖x‖ = 1})
    (sphere_compact : IsCompact {x : Fin (n + 1) → ℝ | ‖x‖ = 1})
    (sphere_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
      Continuous ν ∧ ∀ p ∈ ({x : Fin (n + 1) → ℝ | ‖x‖ = 1} : Set _), ‖ν p‖ = 1) :
    SmoothMapBetweenHypersurfaces n where
  φ := f.φ
  φ_smooth := f.φ_smooth
  M := f.M
  M_compact := f.M_compact
  M_hypersurface := f.M_hypersurface
  M_oriented := f.M_oriented
  M_tilde := {x : Fin (n + 1) → ℝ | ‖x‖ = 1}
  M_tilde_compact := sphere_compact
  M_tilde_connected := sphere_connected
  M_tilde_hypersurface := sphere_hypersurface
  M_tilde_oriented := sphere_oriented
  φ_maps_to_target := fun p hp => by
    simp only [Set.mem_setOf_eq]
    exact f.φ_maps_to_sphere p hp

def SmoothMapToSphere.tangentMapDet {n : ℕ}
    (f : SmoothMapToSphere n)
    (p : Fin (n + 1) → ℝ) : ℝ :=

  let ν_tilde := f.φ p

  let chartData := Classical.epsilon (fun (data : (Fin n → ℝ) × ((Fin n → ℝ) → Fin (n + 1) → ℝ)) =>
    let u := data.1
    let σ := data.2
    σ u = p)
  let u := chartData.1
  let σ := chartData.2
  jacobianDetAtPoint f.φ σ u ν_tilde

def degreeOfMapReal {n : ℕ} (f : SmoothMapToSphere n) : ℝ :=
  let μ := MeasureTheory.Measure.hausdorffMeasure (↑n : ℝ)
  (1 / sphereVolume n) *
    ∫ p in f.M, f.tangentMapDet p ∂μ

def degreeOfMap {n : ℕ} (f : SmoothMapToSphere n) : ℤ :=
  ⌊degreeOfMapReal f + 1 / 2⌋


end GaussMapDegree
end
