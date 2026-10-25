/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterBridgeCalculus.Part2
open Finset Filter
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


def replicaAgreementTiltProb
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) (q : ConfigSpace V) : Real :=
  ghsiAgreementProb G J hf q *
      Real.exp (r * replicaAgreementSpin sites q) /
    replicaBridgeMoment G J hf sites r


def replicaAgreementTiltVariance
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  (∑ q : ConfigSpace V, replicaAgreementTiltProb G J hf sites r q *
      replicaAgreementSpin sites q ^ 2) -
    (∑ q : ConfigSpace V, replicaAgreementTiltProb G J hf sites r q *
      replicaAgreementSpin sites q) ^ 2

end
end StatMech.Ising
