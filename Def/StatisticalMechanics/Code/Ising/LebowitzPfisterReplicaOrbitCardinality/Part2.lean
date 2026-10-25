/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitGateFamily
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCardinality.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaOrbitConfigurationWeight
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (x : LPReplicaOrbitConfiguration G sites A B q) : Real :=
  weight (lpReplicaCurrentGraph G sites) beta
      (lpReplicaCurrentCoupling J hf r)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) x.2.1.1) *
    weight (lpReplicaCurrentGraph G sites) beta
      (lpReplicaCurrentCoupling J hf r)
      (ofEdgeFun (lpReplicaCurrentGraph G sites)
        (lpReplicaReflectedResidual G sites x.1.1 x.2.1.1))


end
end StatMech.Ising
