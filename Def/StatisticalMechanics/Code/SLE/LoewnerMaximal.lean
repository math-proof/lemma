/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Structure.StatisticalMechanics.Code.SLE.LoewnerMaximal
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

def LoewnerForwardSolution.restrict {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (g : LoewnerForwardSolution W z T) {S : ℝ} (hST : S ≤ T) :
    LoewnerForwardSolution W z S where
  curve := g.curve
  initial := g.initial
  deriv := by
    intro t ht
    exact (g.deriv t ⟨ht.1, ht.2.trans hST⟩).mono (Icc_subset_Icc_right hST)
  upper := by
    intro t ht
    exact g.upper t ⟨ht.1, ht.2.trans hST⟩


end StatMech.SLE
