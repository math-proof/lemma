/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementMarginalRatio.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementComplementRatio
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementMarginalRatio
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def ghsiSubsetMarginalMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (M P : Finset V) : Real :=
  ∑ S ∈ Mᶜ.powerset, ghsiSubsetMass G K hf (P ∪ S)

end
end StatMech.Ising
