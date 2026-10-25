/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorFrozenExteriorGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y :=
    (H.Adj x y ∧
      ¬ (rlc_connectorFiniteGraph gamma gamma').Adj x y ∧
      psi s(x, y) = true) ∨ B.Adj x y
  symm := by
    constructor
    rintro x y (hxy | hxy)
    · left
      exact ⟨hxy.1.symm, fun hyx => hxy.2.1 hyx.symm,
        by simpa [Sym2.eq_swap] using hxy.2.2⟩
    · exact Or.inr hxy.symm
  loopless := ⟨by
    rintro x (hxx | hxx)
    · exact (H.ne_of_adj hxx.1) rfl
    · exact (B.ne_of_adj hxx) rfl⟩

end
end StatMech.Universality
