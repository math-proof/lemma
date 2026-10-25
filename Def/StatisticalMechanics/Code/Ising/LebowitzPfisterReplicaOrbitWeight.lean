/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRepresentatives.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitWeight
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaProfileOrbitBaseWeight
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Real :=
  (∏ e ∈ lpReplicaCurrentEdgeOrbitFixed G sites,
      (beta * lpReplicaCurrentCoupling J hf r e.1) ^ (q e / 2) /
        Nat.factorial (q e / 2)) *
    ∏ e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites,
      (beta * lpReplicaCurrentCoupling J hf r e.1) ^ q e /
        Nat.factorial (q e)


noncomputable def lpReplicaProfileOrbitMultiplicity
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Nat :=
  ∏ e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites,
    Nat.choose (q e) (m e)


end
end StatMech.Ising
