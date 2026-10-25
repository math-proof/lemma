/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardFormanTerm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanTerm


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteCRSFAtomicCycleCoefficient
    (transport : V -> V -> Complex) {next : V -> V}
    (S : finiteCRSFCycleSupport next)
    (cycle : Equiv.Perm (↑S.carrier)) : Complex :=
  -finiteCRSFAtomicCycleHolonomy transport S cycle


end StatMech.FrontierA
