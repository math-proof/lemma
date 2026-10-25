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
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esFree_spin_marginal (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    esFirstMarginal G q (1 - Real.exp (-(β * J))) σ = Potts.pottsProb G q β J σ :=
  esFirstMarginal_eq_pottsProb G q β J σ


theorem esFree_edge_marginal (q : ℕ) (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    esSecondMarginal G q p ω = fkProb G p (q : ℝ) ω :=
  esSecondMarginal_eq_fkProb G q p ω


end IsingFK
end StatMech
