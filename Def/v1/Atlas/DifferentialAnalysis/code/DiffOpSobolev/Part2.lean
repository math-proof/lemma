/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SobolevDerivatives
public import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
public import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
public import Def.v1.Atlas.DifferentialAnalysis.code.SobolevDerivatives
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Class.v1.Atlas.DifferentialAnalysis.code.DiffOpSobolev

@[expose] public section

open scoped SchwartzMap ContDiff FourierTransform
open DifferentialOperators SobolevEmbedding SobolevSpace MvPolynomial Filter Topology MeasureTheory


noncomputable section

namespace DiffOpSobolev

variable (n : ℕ)

def tailMultiIndexSum {n : ℕ} (α : Fin n → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val), α i

end DiffOpSobolev
end
