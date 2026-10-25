/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def edgeSubsetFibreEquiv (K : SimpleGraph V)
    [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) :
    ConfigSpace K.edgeSet ≃
      {rho : ConfigSpace (Sym2 V) // rho ∈ condFibre K.edgeFinset psi} where
  toFun eta := ⟨edgeSubsetFibreConfig K psi eta, by
    rw [mem_condFibre]
    exact edgeSubsetFibreConfig_agreesOff K psi eta⟩
  invFun rho := restrictActive K rho.1
  left_inv eta := edgeSubsetFibreConfig_restrictActive K psi eta
  right_inv rho := by
    apply Subtype.ext
    exact edgeSubsetFibreConfig_restrictActive_eq K psi rho.1
      (mem_condFibre.mp rho.2)


end
end StatMech.FK
