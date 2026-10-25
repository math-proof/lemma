/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.IsingFK.EsWired.Part4
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


omit [DecidableEq V] in

theorem esWeightWired_nonneg {q : ℕ} {b : Fin q} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : 0 ≤ esWeightWired G bdry b p σ ω := by
  unfold esWeightWired
  split
  · exact esWeight_nonneg G hp hp1 σ ω
  · rfl


theorem esWeightWired_sum_omega {q : ℕ} (b : Fin q) (β J : ℝ) (σ : V → Fin q) :
    (∑ ω : ConfigSpace (Sym2 V), esWeightWired G bdry b (1 - Real.exp (-(β * J))) σ ω)
      = esFirstConst G β J * pottsWeightWired G bdry b β J σ := by
  unfold esWeightWired pottsWeightWired
  by_cases h : BoundaryFixed bdry b σ
  · simp only [if_pos h]
    rw [esWeight_sum_eq_pottsWeight]
  · simp only [if_neg h, Finset.sum_const_zero, mul_zero]


end IsingFK
end StatMech
