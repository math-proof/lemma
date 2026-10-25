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
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Cheeger
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Cheeger
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Expanders
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.HallTheorem
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.LovaszSimonovits
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.CanonicalPaths
import Abbrev.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders.Part2
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.HallTheorem.Part2
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.LovaszSimonovits
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.CanonicalPaths
import Mathlib.Analysis.Matrix.Spectrum
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.RandomWalks


namespace RandomWalks

open Matrix SimpleGraph Module.End Finset

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

end NormWalkEigenvalueEquiv
end RandomWalks
