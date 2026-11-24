module
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Def.v1.Atlas.DifferentialAnalysis.code.DistributionalKernels2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.DistributionalKernels2
public import Def.v1.Atlas.DifferentialAnalysis.code.WeightedDerivExpansion


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeightedDerivExpansion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open BigOperators

open scoped SchwartzMap

namespace WeightedDerivExpansion

/-- The componentwise order on multi-indices is decidable. -/
instance {n : ℕ} (α γ : Fin n → ℕ) : Decidable (multiIndexLE α γ) :=
  Fintype.decidableForallFintype

end WeightedDerivExpansion
end
