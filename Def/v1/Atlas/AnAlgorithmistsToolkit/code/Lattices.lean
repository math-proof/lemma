/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Lattices.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho


noncomputable section

open MeasureTheory MeasureTheory.Measure Submodule Module ZSpan Set Metric

namespace Lattices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def IsReducedBasis (u v : E) : Prop :=
  ‖u‖ ≤ ‖v‖ ∧ 2 * |@inner ℝ E _ u v| ≤ ‖u‖ ^ 2

def IsLatticeVector (u v : E) (w : E) : Prop :=
  ∃ a b : ℤ, w = (a : ℝ) • u + (b : ℝ) • v

def gramSchmidtCoeff (f : Fin n → E) (i k : Fin n) : ℝ :=
  @inner ℝ E _ (gramSchmidt ℝ f k) (f i) / (‖gramSchmidt ℝ f k‖ ^ 2)

end Lattices
end
