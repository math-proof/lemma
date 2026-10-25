/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Abbrev.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

def IsSymmetricPair {u₁ v₁ u₂ v₂ : Site 2}
    (γ₁ : LatticePath u₁ v₁) (γ₂ : LatticePath u₂ v₂) : Prop :=
  diagReflFun '' {z | z ∈ γ₁.support} = {z | z ∈ γ₂.support}


end BeffaraDC
end StatMech
