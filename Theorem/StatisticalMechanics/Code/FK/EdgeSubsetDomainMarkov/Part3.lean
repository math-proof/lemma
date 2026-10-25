/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov.Part5
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem numClustersBC_edgeSubsetFibre_eq_induced
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V))
    (eta : ConfigSpace K.edgeSet) :
    numClustersBC H B (edgeSubsetFibreConfig K psi eta) =
      numClustersBC K (edgeSubsetInducedWiring K H B psi)
        (extendActive K eta) := by
  unfold numClustersBC
  rw [openSub_edgeSubsetFibre_sup_frozen K H B hKH psi eta]
  exact Nat.card_congr (edgeSubsetExteriorComponentEquiv K H B psi
    (openSub K (extendActive K eta)))


end
end StatMech.FK
