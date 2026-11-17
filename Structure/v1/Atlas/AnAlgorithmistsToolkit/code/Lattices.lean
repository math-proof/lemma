/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Lattices.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Lattices


public noncomputable section

open MeasureTheory MeasureTheory.Measure Submodule Module ZSpan Set Metric

namespace Lattices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

structure IsLLLReduced (f : Fin n → E) : Prop where
  sizeReduced : ∀ (i k : Fin n), k < i → |gramSchmidtCoeff f i k| ≤ 1 / 2
  lovasz : ∀ (i : Fin n) (hi : i.val + 1 < n),
    ‖gramSchmidt ℝ f i‖ ^ 2 ≤
      4 / 3 * ‖gramSchmidt ℝ f ⟨i.val + 1, hi⟩ +
        gramSchmidtCoeff f ⟨i.val + 1, hi⟩ i • gramSchmidt ℝ f i‖ ^ 2

end Lattices
end
