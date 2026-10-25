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
open MeasureTheory
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice StatMech.Ising StatMech.Percolation


section AbstractGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def isingBond (σ : V → Fin 2) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y => isingSpin (σ x) * isingSpin (σ y), fun _ _ => mul_comm _ _⟩ e

end AbstractGraph
end IsingFK
end StatMech
