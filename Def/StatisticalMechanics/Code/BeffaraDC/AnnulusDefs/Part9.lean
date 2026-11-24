module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
public import Structure.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs
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

namespace SymmetricDomain

variable (D : SymmetricDomain)


def wired : Set (Site 2) :=
  {z | z ∈ D.γ₁.support} ∪ {z | z ∈ D.γ₂.support}


def free : Set (Site 2) := D.G \ D.wired


end SymmetricDomain
end BeffaraDC
end StatMech
