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
import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part9
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

namespace SymmetricDomain

variable (D : SymmetricDomain)


def Connected (D : SymmetricDomain) (ω : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ∃ (x : {z | z ∈ D.γ₁.support}) (y : {z | z ∈ D.γ₂.support}),
    ConnectedWithin 2 ω D.G
      ⟨(x : Site 2), D.γ₁_subset x.2⟩ ⟨(y : Site 2), D.γ₂_subset y.2⟩


def connectionEvent (D : SymmetricDomain) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | D.Connected ω}

end SymmetricDomain
end BeffaraDC
end StatMech
