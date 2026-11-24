module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
public import Theorem.StatisticalMechanics.Code.FK.EdwardsSokalFull
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def pottsAgreeProb (q : ℕ) (β J : ℝ) (x y : V) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : V → Fin q => σ x = σ y), Potts.pottsProb G q β J σ


end FK
end StatMech
