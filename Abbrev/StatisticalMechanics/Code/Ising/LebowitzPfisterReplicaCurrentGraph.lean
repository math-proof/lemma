module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

abbrev LPReplicaCurrentVertex (V : Type*) := (V ⊕ V) ⊕ Bool


end
end StatMech.Ising
