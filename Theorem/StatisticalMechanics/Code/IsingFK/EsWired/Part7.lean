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
import Def.StatisticalMechanics.Code.IsingFK.EsWired.Part6
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


theorem esWiredFirstMarginal_eq_pottsProbWired {q : ℕ} [NeZero q] (b : Fin q) (β J : ℝ)
    (σ : V → Fin q) :
    esWiredFirstMarginal G bdry q b (1 - Real.exp (-(β * J))) σ
      = pottsProbWired G bdry q b β J σ := by
  unfold esWiredFirstMarginal pottsProbWired
  rw [esWeightWired_sum_omega, esZWired_eq_pottsZWired,
    mul_div_mul_left _ _ (esFirstConst_pos G β J).ne']


end IsingFK
end StatMech
