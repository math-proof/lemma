module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
public import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs
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

def IsAnnulusCircuit (ω : ConfigSpace (Sym2 (Site 2))) (n N : ℕ)
    {x : Site 2} (w : (openSubgraph 2 ω).Walk x x) : Prop :=
  w.IsCircuit ∧ ∀ y ∈ w.support, y ∈ annulus n N

end BeffaraDC
end StatMech
