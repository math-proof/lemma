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
import Def.StatisticalMechanics.Code.FK.EdwardsSokal.Part3
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem card_constOnOpen {q : ℕ} (ω : ConfigSpace (Sym2 V)) :
    Nat.card {σ : V → Fin q // ConstOnOpen G ω σ} = q ^ numClusters G ω := by
  classical
  rw [Nat.card_congr (constOnOpenEquiv G ω).symm]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  rfl


theorem esWeight_sum {q : ℕ} (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    (∑ σ : V → Fin q, esWeight G p σ ω) = fkWeight G p (q : ℝ) ω := by
  classical
  have hfac : (∑ σ : V → Fin q, esWeight G p σ ω)
      = edgeProduct G p ω * ∑ σ : V → Fin q, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [esWeight_factor, monoProd_eq_indicator]
  rw [hfac, Finset.sum_boole]
  unfold fkWeight
  congr 1
  have hcard : ({x | ConstOnOpen G ω x} : Finset (V → Fin q)).card = q ^ numClusters G ω := by
    rw [← card_constOnOpen G ω, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  push_cast
  rfl


end FK
end StatMech
