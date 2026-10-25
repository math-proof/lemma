/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementMarginalRatio.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeActual.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeMarginalRank
open Finset SimpleGraph


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def ghsiAgreementMarginalProb
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (M P : Finset V) : Real :=
  ∑ q ∈ (Finset.univ : Finset (ConfigSpace V)).filter
      (fun q => ghsLAgreeFinset q ∩ M = P),
    ghsiAgreementProb G J hf q


end
end StatMech.Ising
