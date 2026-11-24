module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
public import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
public import Def.StatisticalMechanics.Code.Ising.InfiniteVolume.Part5
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


lemma fvProb_nonneg (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    0 ≤ fvProb η n B β h τ :=
  div_nonneg (fvWeight_nonneg η n B β h τ) (fvZ_pos η n B β h).le

lemma fvProb_sum_eq_one (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    ∑ τ : {x // x ∈ box d n} → Bool, fvProb η n B β h τ = 1 := by
  unfold fvProb
  rw [← Finset.sum_div, div_eq_one_iff_eq (fvZ_ne_zero η n B β h)]
  rfl


end Ising
end StatMech
