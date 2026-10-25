/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.EsCorrelations.Part5
open scoped BigOperators

set_option linter.style.show false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esTwoPoint_eq_connProb (p : ℝ) (x y : V) :
    esTwoPoint G p x y = connProb G p 2 x y := by
  classical
  unfold esTwoPoint connProb fkProb
  rw [Finset.sum_congr rfl (fun ω _ => spinProd_sum_eq G p ω x y)]
  rw [esZ_eq_fkZ, Nat.cast_ofNat, Finset.sum_div]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y)]
  have h0 : (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ Connected G ω x y),
        (if Connected G ω x y then fkWeight G p (2 : ℝ) ω else 0) / fkZ G p 2) = 0 := by
    apply Finset.sum_eq_zero
    intro ω hω
    rw [if_neg (Finset.mem_filter.1 hω).2, zero_div]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [if_pos (Finset.mem_filter.1 hω).2]


theorem connProb_eq_sum_fkProb (p q : ℝ) (x y : V) :
    connProb G p q x y =
      ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => Connected G ω x y),
        fkProb G p q ω :=
  rfl

end FK
end StatMech
