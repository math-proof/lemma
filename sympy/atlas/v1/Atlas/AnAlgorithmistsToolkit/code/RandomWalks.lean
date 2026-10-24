/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.Cheeger
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Cheeger
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Expanders
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.HallTheorem
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.LovaszSimonovits
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.CanonicalPaths
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.HallTheorem
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.LovaszSimonovits
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.CanonicalPaths
import Mathlib.Analysis.Matrix.Spectrum

namespace RandomWalks

open Matrix SimpleGraph Module.End Finset

section StationaryDist

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def stationaryDist (v : V) : ℝ :=
  (G.degree v : ℝ) / (∑ u : V, (G.degree u : ℝ))

noncomputable def walkMatrix : Matrix V V ℝ :=
  fun i j => (G.adjMatrix ℝ i j) / (G.degree j : ℝ)

noncomputable def stationaryVec : V → ℝ :=
  fun v => (G.degree v : ℝ) / (∑ u : V, (G.degree u : ℝ))

noncomputable def rwMatrixGen : Matrix V V ℝ :=
  G.adjMatrix ℝ * Matrix.diagonal (fun v => (G.degree v : ℝ)⁻¹)

noncomputable def normWalkMatrix : Matrix V V ℝ :=
  Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) *
    G.adjMatrix ℝ *
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)

noncomputable def lazyRwMatrixGen : Matrix V V ℝ :=
  (2 : ℝ)⁻¹ • (1 + G.adjMatrix ℝ * Matrix.diagonal (fun v => (G.degree v : ℝ)⁻¹))

noncomputable def normLazyWalkMatrix : Matrix V V ℝ :=
  (2 : ℝ)⁻¹ • (1 +
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) *
    G.adjMatrix ℝ *
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹))

variable (d : ℕ)

noncomputable def lazyRwMatrix : Matrix V V ℝ :=
  (2 : ℝ)⁻¹ • (1 + (d : ℝ)⁻¹ • G.adjMatrix ℝ)

end LazyWalk

section LazySymmetry

variable {V : Type*} [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def l2Norm {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  Real.sqrt (∑ v : V, (f v) ^ 2)

noncomputable def l2Dist {V : Type*} [Fintype V] (p q : V → ℝ) : ℝ :=
  l2Norm (p - q)

end L2Dist


section Convergence

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

end Convergence


section MixingBound

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

end MixingBound

section NormWalkEigenvalueEquiv

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

lemma sqrtDeg_mul_sqrtDeg_inv
    (hpos : ∀ v : V, 0 < G.degree v) :
    Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) *
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hpos i))
  · rfl

lemma sqrtDeg_inv_mul_sqrtDeg
    (hpos : ∀ v : V, 0 < G.degree v) :
    Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹) *
    Matrix.diagonal (fun v => Real.sqrt (G.degree v : ℝ)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hpos i))
  · rfl

noncomputable def sqrtDegEquiv
    (hpos : ∀ v : V, 0 < G.degree v) : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
  Matrix.toLin'OfInv (sqrtDeg_inv_mul_sqrtDeg G hpos) (sqrtDeg_mul_sqrtDeg_inv G hpos)
