module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
public import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
public import Def.StatisticalMechanics.Code.Ising.InfiniteVolume.Part4
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


lemma fvZ_pos (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : 0 < fvZ η n B β h := by
  unfold fvZ
  apply Finset.sum_pos
  · intro τ _; exact fvWeight_pos η n B β h τ
  · exact Finset.univ_nonempty

lemma fvZ_ne_zero (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) : fvZ η n B β h ≠ 0 :=
  (fvZ_pos η n B β h).ne'


end Ising
end StatMech
