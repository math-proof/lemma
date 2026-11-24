module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
public import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
public import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.Sharpness.EdwardsSokalClose
open scoped BigOperators
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def esAgreeProb (q : ℕ) (p : ℝ) (x y : V) : ℝ :=
  (∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin q,
      esWeight G p σ ω * (if σ x = σ y then (1:ℝ) else 0)) / esZ G q p


noncomputable def esk_pottsAgreeProb (q : ℕ) (β J : ℝ) (x y : V) : ℝ :=
  ∑ σ : V → Fin q, Potts.pottsProb G q β J σ * (if σ x = σ y then (1:ℝ) else 0)


end FK
end StatMech
