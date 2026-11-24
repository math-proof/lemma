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


theorem fld_separate_of_outward_far (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y a a' : Site d}
    (hxT : x ∈ tfc_trifFinset ω n) (hyT : y ∈ tfc_trifFinset ω n) (hxy : x ≠ y)
    (haout : ∀ z ∈ tfc_trifFinset ω n, z ≠ x → ¬ Connected d (removeSite x ω) a z)
    (hfar : Connected d (removeSite x ω) a' y) :
    ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) a a' := by
  intro haa'
  
  have haa'_single : Connected d (removeSite x ω) a a' :=
    connected_mono (daep2_removeSites_le_removeSite (tfc_trifFinset ω n) ω hxT) haa'
  
  exact haout y hyT (Ne.symm hxy) (haa'_single.trans hfar)


end Percolation
end StatMech
