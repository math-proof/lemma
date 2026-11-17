/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Abbrev.v1.Atlas.AnAlgorithmistsToolkit.code.SpectraCommonGraphs

@[expose] public section

namespace SpectraCommonGraphs

open Real SimpleGraph Matrix

noncomputable section

def ringEigenvalue (n : ℕ) (k : ℕ) : ℝ :=
  2 - 2 * Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ))

def cosEigenvector (n : ℕ) (k : ℕ) (u : Fin n) : ℝ :=
  Real.cos (2 * Real.pi * (k : ℝ) * (u.val : ℝ) / (n : ℝ))

def sinEigenvector (n : ℕ) (k : ℕ) (u : Fin n) : ℝ :=
  Real.sin (2 * Real.pi * (k : ℝ) * (u.val : ℝ) / (n : ℝ))

def vecTensor {V W : Type*} (v : V → ℝ) (w : W → ℝ) : V × W → ℝ :=
  fun p => v p.1 * w p.2

end
end SpectraCommonGraphs
