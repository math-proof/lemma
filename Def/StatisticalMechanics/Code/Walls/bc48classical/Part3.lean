module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
public import Theorem.StatisticalMechanics.Code.Walls.bc47trifarms.Part6
public import Theorem.StatisticalMechanics.Code.Walls.bc46funnelproof.Part6
public import Theorem.StatisticalMechanics.Code.Walls.bc48classical.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
set_option linter.style.longLine false
set_option maxRecDepth 4000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc48_ClassicalBoundaryArmInjection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ φ : Site d → Site d,
    (∀ x, x ∈ box d n → bc47_IsClassicalTrifurcation ω x → φ x ∈ vertexBoundary d n) ∧
    (∀ x, x ∈ box d n → bc47_IsClassicalTrifurcation ω x → ∀ y, y ∈ box d n →
      bc47_IsClassicalTrifurcation ω y → φ x = φ y → x = y)


end StatMech.Walls
