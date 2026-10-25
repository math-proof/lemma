/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
open Finset Filter
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


def replicaBridgeInteraction (sites : I -> V)
    (a b : ConfigSpace V) : Real :=
  ∑ i : I, spin a (sites i) * spin b (sites i)


def replicaAgreementSpin (sites : I -> V) (q : ConfigSpace V) : Real :=
  ∑ i : I, spin q (sites i)


def replicaBridgeMonomial (sites : I -> V) (S : Finset I)
    (s : ConfigSpace V) : Real :=
  ∏ i ∈ S, spin s (sites i)

end
end StatMech.Ising
