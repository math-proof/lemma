module
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Real.Basic
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Cheeger
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Cheeger
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Expanders
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.HallTheorem
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.LovaszSimonovits
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.CanonicalPaths
public import Abbrev.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders.Part2
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.HallTheorem.Part2
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.LovaszSimonovits
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.CanonicalPaths
public import Mathlib.Analysis.Matrix.Spectrum
public import Theorem.v1.Atlas.AnAlgorithmistsToolkit.code.RandomWalks


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RandomWalks.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace RandomWalks

open Matrix SimpleGraph Module.End Finset

section NormWalkEigenvalueEquiv

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def sqrtDegEquiv
    (hpos : ∀ v : V, 0 < G.degree v) : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
  Matrix.toLin'OfInv (sqrtDeg_inv_mul_sqrtDeg G hpos) (sqrtDeg_mul_sqrtDeg_inv G hpos)

end NormWalkEigenvalueEquiv
end RandomWalks
