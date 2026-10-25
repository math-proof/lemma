/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.Part3
open Finset


namespace StatMech.Ising

noncomputable section

def fourBridgePointwiseCutCounterexampleWeight
    (P : Finset (Fin 4)) : Nat :=
  if (∑ i ∈ P, 2 ^ i.val) ∈ ({1, 3, 15} : Finset Nat) then 1 else 0


end
end StatMech.Ising
