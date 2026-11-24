module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.ForestAcyclicityClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.FacPairwiseClose
public import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.RootedTreeSelectorClose
public import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.ForestColouringClose2.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


def rfp_ClawArmGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ x₀ : Site d, x₀ ∈ box d n ∧ IsTrifurcation d ω x₀ ∧
    ∀ b : Site d → Site d,
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite →
      ∃ z, z ∈ box d n ∧ IsTrifurcation d ω z ∧ x₀ ≠ z ∧ Connected d ω x₀ z ∧
        Connected d (removeSite x₀ ω) (b x₀) z ∧
        ¬ Connected d (removeSite z ω) (b x₀) x₀


end Percolation
end StatMech
