/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part17


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteCRSFFixedPointEquivComplement {next : V -> V}
    (S : finiteCRSFCycleSupport next) :
    laplacianPermutationFixedPoint S.ambientPerm ≃
      {v : V // v ∉ S.carrier} where
  toFun v := ⟨v, by
    intro hv
    exact S.ambientPerm_ne_of_mem hv v.property⟩
  invFun v := ⟨v, S.ambientPerm_apply_of_not_mem v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl


noncomputable def finiteCRSFOutgoingConductance
    (conductance : V -> V -> Complex) (next : V -> V) : Complex :=
  ∏ v : V, conductance v (next v)


noncomputable def finiteCRSFSupportTransport
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next) : Complex :=
  Equiv.Perm.sign S.ambientPerm •
    ∏ v ∈ S.carrier, -transport v (next v)


noncomputable def finiteCRSFAtomicCycleHolonomy
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next)
    (cycle : Equiv.Perm (↑S.carrier)) : Complex :=
  ∏ v ∈ cycle.support, transport v (next v)


end StatMech.FrontierA
