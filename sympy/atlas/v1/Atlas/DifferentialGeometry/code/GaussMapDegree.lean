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

noncomputable section

open scoped Matrix

namespace GaussMapDegree

def gramMatrix (n : ℕ) (σ : (Fin n → ℝ) → (Fin (n + 1) → ℝ))
    (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let Dσ := fderiv ℝ σ u
  fun i j =>
    ∑ k : Fin (n + 1), Dσ (Function.update 0 i 1) k * Dσ (Function.update 0 j 1) k

def augmentedMatrix {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin n) ℝ)
    (ν : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if h : (j : ℕ) < n then B i ⟨j, h⟩
    else ν i

structure SmoothHypersurfaceMap (n : ℕ) where
  domainU : Set (Fin n → ℝ)
  domainU_open : IsOpen domainU
  domainV : Set (Fin n → ℝ)
  domainV_open : IsOpen domainV
  σ : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  τ : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  σ_smooth : ContDiffOn ℝ ⊤ σ domainU
  σ_immersion : ∀ u ∈ domainU, Function.Injective (fderiv ℝ σ u)
  τ_smooth : ContDiffOn ℝ ⊤ τ domainV
  τ_immersion : ∀ v ∈ domainV, Function.Injective (fderiv ℝ τ v)
  h : (Fin n → ℝ) → (Fin n → ℝ)
  h_maps : ∀ u ∈ domainU, h u ∈ domainV
  h_smooth : ContDiffOn ℝ ⊤ h domainU
  chain_rule : ∀ u ∈ domainU,
    (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => fderiv ℝ σ u (Function.update 0 j 1) i) *
      (Matrix.of fun (i : Fin n) (j : Fin n) => fderiv ℝ h u (Function.update 0 j 1) i) =
    (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => fderiv ℝ (τ ∘ h) u (Function.update 0 j 1) i)
  ν : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  ν_tilde : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  ν_orth : ∀ u ∈ domainU, ∀ j : Fin n,
    ∑ i : Fin (n + 1), fderiv ℝ σ u (Function.update 0 j 1) i * ν u i = 0
  ν_norm : ∀ u ∈ domainU, ∑ i : Fin (n + 1), ν u i ^ 2 = 1
  ν_tilde_orth : ∀ v ∈ domainV, ∀ j : Fin n,
    ∑ i : Fin (n + 1), fderiv ℝ τ v (Function.update 0 j 1) i * ν_tilde v i = 0
  ν_tilde_norm : ∀ v ∈ domainV, ∑ i : Fin (n + 1), ν_tilde v i ^ 2 = 1
  σ_pos_oriented : ∀ u ∈ domainU,
    0 < (augmentedMatrix (fun i j => fderiv ℝ σ u (Function.update 0 j 1) i)
      (ν u)).det
  τ_pos_oriented : ∀ v ∈ domainV,
    0 < (augmentedMatrix (fun i j => fderiv ℝ τ v (Function.update 0 j 1) i)
      (ν_tilde v)).det

def SmoothHypersurfaceMap.jacobianMatrix {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ Φ.h u (Function.update 0 j 1) i

def SmoothHypersurfaceMap.jacobianDet {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : ℝ :=
  (Φ.jacobianMatrix u).det

def SmoothHypersurfaceMap.sourceJacobian {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun i j => fderiv ℝ Φ.σ u (Function.update 0 j 1) i

def SmoothHypersurfaceMap.composedJacobian {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun i j => fderiv ℝ (Φ.τ ∘ Φ.h) u (Function.update 0 j 1) i

def IsSmHypersurface (n : ℕ) (M : Set (Fin (n + 1) → ℝ)) : Prop :=
  ∀ p ∈ M, ∃ (U : Set (Fin n → ℝ)) (σ : (Fin n → ℝ) → Fin (n + 1) → ℝ),
    IsOpen U ∧ ContDiffOn ℝ ⊤ σ U ∧
    (∀ u ∈ U, Function.Injective (fderiv ℝ σ u)) ∧
    p ∈ σ '' U ∧ σ '' U ⊆ M

structure SmoothMapBetweenHypersurfaces (n : ℕ) where
  φ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)
  φ_smooth : ContDiff ℝ ⊤ φ
  M : Set (Fin (n + 1) → ℝ)
  M_compact : IsCompact M
  M_hypersurface : IsSmHypersurface n M
  M_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
    Continuous ν ∧ ∀ p ∈ M, ‖ν p‖ = 1
  M_tilde : Set (Fin (n + 1) → ℝ)
  M_tilde_compact : IsCompact M_tilde
  M_tilde_connected : IsConnected M_tilde
  M_tilde_hypersurface : IsSmHypersurface n M_tilde
  M_tilde_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
    Continuous ν ∧ ∀ p ∈ M_tilde, ‖ν p‖ = 1
  φ_maps_to_target : ∀ p ∈ M, φ p ∈ M_tilde

def hypersurfaceVolume (n : ℕ) (S : Set (Fin (n + 1) → ℝ)) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure (↑n : ℝ) S).toReal

structure SmoothMapToSphere (n : ℕ) where
  φ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)
  φ_smooth : ContDiff ℝ ⊤ φ
  M : Set (Fin (n + 1) → ℝ)
  M_compact : IsCompact M
  M_hypersurface : IsSmHypersurface n M
  M_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
    Continuous ν ∧ ∀ p ∈ M, ‖ν p‖ = 1
  φ_maps_to_sphere : ∀ p ∈ M, ‖φ p‖ = 1

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
