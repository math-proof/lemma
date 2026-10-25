/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanTerm.Part2


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteCRSFAmbientAtomicCycleHolonomy
    (transport : V -> V -> Complex) {next : V -> V}
    (cycle : finiteCRSFAtomicCycle next) : Complex :=
  ∏ v ∈ cycle.1.support, transport v (next v)


end StatMech.FrontierA
