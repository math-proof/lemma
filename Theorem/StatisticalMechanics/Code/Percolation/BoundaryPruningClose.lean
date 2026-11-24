module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoundaryPruningClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bpr_treeForestData_slh_refutable (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ¬ slh_TreeForestData ω n := by
  classical
  rintro ⟨W, _, _, G, _, π, ιT, sec, lamL, hTree, hWcard, hπ, hπinj,
    hπιT, hιinj, hsec, hlammap, hlaminj⟩
  
  have hinf : (cluster d ω x).Infinite := tfc_trif_cluster_infinite ω x htri
  
  have hinjOn : Set.InjOn (sec x) (cluster d ω x) := by
    intro a ha b hb hab
    obtain ⟨hπa, _, _⟩ := hsec x hxbox htri a ha
    obtain ⟨hπb, _, _⟩ := hsec x hxbox htri b hb
    rw [← hπa, ← hπb, hab]
  
  exact (hinf.image hinjOn) (Set.toFinite _)


end Percolation
end StatMech
