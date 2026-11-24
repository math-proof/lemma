module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.ClusterDualContour
public import Theorem.StatisticalMechanics.Code.Percolation.DiscreteJordanSeparationFalse
public import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


def djfx_DiscreteJordanSeparation' : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → ∀ {a b : Site 2},
    (∃ a' : Site 2, (faceBoundaryGraph K).Adj a a') →
    (faceBoundaryGraph K).Reachable a b →
      ∃ c : (faceBoundaryGraph K).Walk a a, c.IsCycle ∧ b ∈ c.support


end Percolation
end StatMech
