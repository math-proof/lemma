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
public import Theorem.StatisticalMechanics.Code.Percolation.ForestColouringClose2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


open Classical in


noncomputable def fcc_colorRep (ω : ConfigSpace (Sym2 (Site d))) (c : Site d → Site d → Fin 3)
    (y : Site d) (i : Fin 3) : Site d :=
  if h : ∃ w, Connected d ω y w ∧ y ≠ w ∧ c y w = i then h.choose else y


end Percolation
end StatMech
