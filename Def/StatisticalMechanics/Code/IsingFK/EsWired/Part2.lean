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
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part2
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def pottsWeightWired {q : ℕ} (b : Fin q) (β J : ℝ) (σ : V → Fin q) : ℝ :=
  if BoundaryFixed bdry b σ then Potts.pottsWeight G β J σ else 0


noncomputable def pottsZWired (q : ℕ) (b : Fin q) (β J : ℝ) : ℝ :=
  ∑ σ : V → Fin q, pottsWeightWired G bdry b β J σ


end IsingFK
end StatMech
