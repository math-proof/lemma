/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RVTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.ConvexGeometry.Part2
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.ConvexGeometry
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Probability.Independence.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

open Set

open scoped Matrix.Norms.Frobenius


noncomputable section

open MeasureTheory Real Finset

namespace RudelsonVershynin

def vecOuterProduct {n : ℕ} (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => v i * v j

def euclideanNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, v i ^ 2)

end RudelsonVershynin
end
