/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/LindebergHybrid.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.BooleanFunctions.code.InvarianceDefs
public import Instance.v1.Atlas.BooleanFunctions.code.LindebergHybrid

@[expose] public section

noncomputable section

open MeasureTheory Measure Finset BigOperators ENNReal

namespace BooleanFourier

def hybridMeasure (n : ℕ) (k : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i : Fin n =>
    if i.val < k then ProbabilityTheory.gaussianReal 0 1 else rademacherMeasure)

def hybridExpectation {n : ℕ} (f : (Fin n → Bool) → ℝ) (Ψ : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ z : Fin n → ℝ, Ψ (multilinearExtension f z) ∂(hybridMeasure n k)

def boolToRealVec {n : ℕ} (b : Fin n → Bool) : Fin n → ℝ :=
  fun i => boolToReal (b i)

end BooleanFourier
end
