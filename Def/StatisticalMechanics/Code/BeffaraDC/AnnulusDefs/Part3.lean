module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
public import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part2
open Set
open StatMech.Lattice
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace BeffaraDC

def Separates (C : Set (Site 2)) (n N : ℕ) : Prop :=
  ∀ (u v : Site 2), u ∈ box 2 n → v ∉ box 2 N →
    ∀ (p : (hypercubicLattice 2).Walk u v), ∃ z ∈ p.support, z ∈ C


end BeffaraDC
end StatMech
