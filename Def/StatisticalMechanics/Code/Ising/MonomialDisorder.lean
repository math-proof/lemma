/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MonomialDisorder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.Ising

noncomputable section

variable {V P : Type*} [Fintype V] [DecidableEq V]
  [Fintype P] [DecidableEq P]


def monomialInteractionPartition
    (K : P -> Real) (fac : P -> ConfigSpace V -> Real) : Real :=
  ∑ sigma : ConfigSpace V, Real.exp (∑ p : P, K p * fac p sigma)


def reverseInteractionCoupling (K : P -> Real) (D : Finset P) : P -> Real :=
  fun p => if p ∈ D then -K p else K p

end
end StatMech.Ising
