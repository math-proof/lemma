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
public import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafDisjointClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


def fld_OutwardArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x →
    ∃ a, (a ∈ box d n ∧ Connected d ω x a ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) a).Infinite) ∧
      (∀ y ∈ tfc_trifFinset ω n, y ≠ x → ¬ Connected d (removeSite x ω) a y) ∧
      (∀ z ∈ tfc_trifFinset ω n, z ≠ x → Connected d (removeSite z ω) a x)


end Percolation
end StatMech
