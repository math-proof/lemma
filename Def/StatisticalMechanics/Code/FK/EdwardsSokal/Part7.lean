/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part6
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def esSecondMarginal (q : ℕ) (p : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  (∑ σ : V → Fin q, esWeight G p σ ω) / esZ G q p


noncomputable def esFirstMarginal (q : ℕ) (p : ℝ) (σ : V → Fin q) : ℝ :=
  (∑ ω : ConfigSpace (Sym2 V), esWeight G p σ ω) / esZ G q p


end FK
end StatMech
