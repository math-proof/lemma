/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph.Part4
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaCurrentSeamEdge (sites : I -> V) (i : I) :
    Sym2 (LPReplicaCurrentVertex V) :=
  s(lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i)

end
end StatMech.Ising
