/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsInfinite.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding
open MeasureTheory
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice StatMech.Ising StatMech.Percolation


section AbstractGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def isingWiredWeight (β : ℝ) (σ : V → Fin 2) : ℝ :=
  if BoundaryFixed bdry (0 : Fin 2) σ then
    Real.exp (β * ∑ e ∈ G.edgeFinset, isingBond σ e) else 0


noncomputable def isingWiredZ (β : ℝ) : ℝ := ∑ σ : V → Fin 2, isingWiredWeight G bdry β σ


noncomputable def isingWiredOnePoint (β : ℝ) (x : V) : ℝ :=
  (∑ σ : V → Fin 2, isingWiredWeight G bdry β σ * isingSpin (σ x)) / isingWiredZ G bdry β

end AbstractGraph
end IsingFK
end StatMech
