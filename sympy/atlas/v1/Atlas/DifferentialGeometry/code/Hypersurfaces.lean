/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Topology.Connected.Basic

noncomputable section

open Matrix Finset BigOperators

structure HypersurfacePatch (n : ℕ) where
  domain : Set (Fin n → ℝ)
  domain_open : IsOpen domain
  f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  smooth : ContDiffOn ℝ ⊤ f domain
  immersion : ∀ x ∈ domain, Function.Injective (fderiv ℝ f x)

variable {n : ℕ}

def HypersurfacePatch.partialDeriv (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i : Fin n) : Fin (n + 1) → ℝ :=
  fderiv ℝ patch.f x (Pi.single i 1)

def generalizedCross {n : ℕ} (v : Fin n → (Fin (n + 1) → ℝ)) :
    Fin (n + 1) → ℝ :=
  fun j => (-1 : ℝ) ^ (j : ℕ) * (Matrix.of (fun (i : Fin n) (k : Fin n) =>
    v i (Fin.succAbove j k))).det

def orientationMatrix (patch : HypersurfacePatch n) (x : Fin n → ℝ)
    (w : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (row : Fin (n + 1)) (col : Fin (n + 1)) =>
    if h : col.val < n then
      patch.partialDeriv x ⟨col.val, h⟩ row
    else
      w row

def gaussNormal (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  let crossVec := generalizedCross (patch.partialDeriv x)
  let nrm := Real.sqrt (crossVec ⬝ᵥ crossVec)
  fun j => crossVec j / nrm

noncomputable def firstFundamentalForm (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let Df := fun i => fderiv ℝ patch.f x (Pi.single i 1)
  Matrix.of (fun i j => (Df i) ⬝ᵥ (Df j))

noncomputable def jacobianMatrix (patch : HypersurfacePatch n) (x : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin n) ℝ :=
  Matrix.of (fun k i => fderiv ℝ patch.f x (Pi.single i 1) k)


open Matrix in
noncomputable def secondFundamentalForm {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j =>
    (fderiv ℝ (fderiv ℝ patch.f · (Pi.single j 1)) x (Pi.single i 1)) ⬝ᵥ
    (gaussNormal patch x))

noncomputable def shapeOperator {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (firstFundamentalForm patch x)⁻¹ * (secondFundamentalForm patch x)

open Matrix in
def IsPrincipalCurvature {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (κ : ℝ) : Prop :=
  (shapeOperator patch x).charpoly.IsRoot κ


noncomputable def meanCurvature {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ) : ℝ :=
  (shapeOperator patch x).trace

noncomputable def gaussCurvature {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ) : ℝ :=
  (shapeOperator patch x).det

noncomputable def scalarCurvature {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ) : ℝ :=
  ((shapeOperator patch x).trace ^ 2 - ((shapeOperator patch x) * (shapeOperator patch x)).trace) / 2

def coordinateJacobian {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ φ x (Pi.single j 1) i

def normalDerivMatrix {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (row : Fin (n + 1)) (col : Fin (n + 1)) =>
    if h : col.val < n then
      fderiv ℝ (gaussNormal patch) x (Pi.single ⟨col.val, h⟩ 1) row
    else
      gaussNormal patch x row

end

noncomputable section

open Matrix Finset BigOperators

def shapeOperatorLinkingMatrix {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (row col : Fin (n + 1)) =>
    if hr : row.val < n then
      if hc : col.val < n then
        -(shapeOperator patch x ⟨row.val, hr⟩ ⟨col.val, hc⟩)
      else 0
    else
      if _hc : col.val < n then 0 else 1

def IsCompactHypersurface {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1)))) : Prop :=
  IsCompact M
