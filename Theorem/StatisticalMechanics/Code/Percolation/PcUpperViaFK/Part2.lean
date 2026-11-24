module
public import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperPeierls
public import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
public import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
public import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
public import Theorem.StatisticalMechanics.Code.FK.Ergodicity
public import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
public import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
public import Def.StatisticalMechanics.Code.Percolation.PcUpperViaFK
open MeasureTheory Filter Topology Set Finset
open scoped NNReal ENNReal BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.FK

variable {d : ℕ}


@[simp] theorem pcv_siteEmbed_castAdd (k : ℕ) (x : Site 2) (i : Fin 2) :
    pcv_siteEmbed k x (Fin.castAdd k i) = x i := by
  simp [pcv_siteEmbed]

@[simp] theorem pcv_siteEmbed_natAdd (k : ℕ) (x : Site 2) (i : Fin k) :
    pcv_siteEmbed k x (Fin.natAdd 2 i) = 0 := by
  simp [pcv_siteEmbed]

theorem pcv_siteEmbed_injective (k : ℕ) : Function.Injective (pcv_siteEmbed k) := by
  intro x y hxy
  funext i
  have := congrFun hxy (Fin.castAdd k i)
  simpa using this


theorem pcv_siteEmbed_adj_iff (k : ℕ) (x y : Site 2) :
    (hypercubicLattice (2 + k)).Adj (pcv_siteEmbed k x) (pcv_siteEmbed k y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_add]
  simp


end Percolation
end StatMech
