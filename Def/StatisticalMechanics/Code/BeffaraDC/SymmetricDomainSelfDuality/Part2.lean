/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Instance.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part2
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

def planarDomain (D : SymmetricDomain) : PlanarZ2Subgraph where
  V := D.Vertex
  finV := inferInstance
  decV := inferInstance
  G := D.finiteGraph
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := by
    intro x y hxy
    exact hxy


def OnGammaOne (D : SymmetricDomain) (x : D.Vertex) : Prop :=
  x.1 ∈ D.γ₁.support


def OnGammaTwo (D : SymmetricDomain) (x : D.Vertex) : Prop :=
  x.1 ∈ D.γ₂.support

end SymmetricDomain
end
end BeffaraDC
end StatMech
