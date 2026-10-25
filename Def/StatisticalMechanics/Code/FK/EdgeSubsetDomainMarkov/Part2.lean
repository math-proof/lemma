/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Instance.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def edgeSubsetInducedWiring
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧
    (edgeSubsetFrozenExteriorGraph K H B psi).Reachable x y
  symm := by
    constructor
    rintro x y ⟨hne, hxy⟩
    exact ⟨hne.symm, hxy.symm⟩
  loopless := ⟨by rintro x ⟨hne, _⟩; exact hne rfl⟩

end
end StatMech.FK
