/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/RVTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AnAlgorithmistsToolkit.code.ConvexGeometry.Part2
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.ConvexGeometry
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Probability.Independence.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
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
