/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Eigenvalues.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

open Module.End


namespace Matrix

variable {n : Type*} [Fintype n]

def IsEigenvectorOf (M : Matrix n n ℝ) (μ : ℝ) (x : n → ℝ) : Prop :=
  M.mulVec x = μ • x ∧ x ≠ 0

noncomputable def eigenspaceOf [DecidableEq n] (M : Matrix n n ℝ) (μ : ℝ) :
    Submodule ℝ (n → ℝ) :=
  eigenspace M.mulVecLin μ

end Matrix
