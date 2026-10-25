/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementMarginalRatio.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeActual.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeMarginalRank.Part2
open Finset SimpleGraph


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def fourBridgeMarkedSet (w x y z : V) : Finset V := {w, x, y, z}


def fourBridgeAgreementSpinMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (w x y z : V) (s : Real) : Real :=
  ∑ q ∈ (Finset.univ : Finset (ConfigSpace V)).filter
      (fun q => replicaAgreementSpin (fourBridgeSites w x y z) q = s),
    ghsiAgreementProb G J hf q

end
end StatMech.Ising
