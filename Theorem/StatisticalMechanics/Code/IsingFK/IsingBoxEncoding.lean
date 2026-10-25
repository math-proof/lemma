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
import Def.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding
open MeasureTheory
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice StatMech.Ising StatMech.Percolation


section AbstractGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem isingBond_mk (σ : V → Fin 2) (x y : V) :
    isingBond σ s(x, y) = isingSpin (σ x) * isingSpin (σ y) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem monoIndicator_eq_isingBond (σ : V → Fin 2) (e : Sym2 V) :
    monoIndicator σ e = isingBond σ e / 2 + 1 / 2 := by
  induction e with
  | _ x y =>
    rw [monoIndicator_mk, isingBond_mk, isingSpin_mul]
    by_cases h : σ x = σ y <;> simp [h] <;> ring

omit [DecidableEq V] in


theorem agreement_eq_isingBondSum (σ : V → Fin 2) :
    agreement G σ
      = (∑ e ∈ G.edgeFinset, isingBond σ e) / 2 + (G.edgeFinset.card : ℝ) / 2 := by
  unfold agreement
  rw [Finset.sum_congr rfl (fun e _ => monoIndicator_eq_isingBond σ e),
    Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, nsmul_eq_mul]
  ring


end AbstractGraph
end IsingFK
end StatMech
