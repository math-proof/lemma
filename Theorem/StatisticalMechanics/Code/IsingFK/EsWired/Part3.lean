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
import Def.StatisticalMechanics.Code.IsingFK.EsWired.Part2
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


theorem pottsZWired_pos (q : ℕ) [NeZero q] (b : Fin q) (β J : ℝ) :
    0 < pottsZWired G bdry q b β J := by
  unfold pottsZWired pottsWeightWired
  apply Finset.sum_pos'
  · intro σ _; split
    · exact (Potts.pottsWeight_pos G β J σ).le
    · rfl
  · exact ⟨fun _ => b, Finset.mem_univ _, by
      rw [if_pos (boundaryFixed_const bdry b)]; exact Potts.pottsWeight_pos G β J _⟩

theorem pottsZWired_ne_zero (q : ℕ) [NeZero q] (b : Fin q) (β J : ℝ) :
    pottsZWired G bdry q b β J ≠ 0 :=
  (pottsZWired_pos G bdry q b β J).ne'


end IsingFK
end StatMech
