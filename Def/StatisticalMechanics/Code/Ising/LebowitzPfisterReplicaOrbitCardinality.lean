/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitGateFamily
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCardinality
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaOrbitConfiguration
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q},
    Σ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
        a <= m.1},
      (↑(lpReplicaDisconnProfileFamily G sites A K.1) ×
        ↑(lpReplicaDisconnProfileFamily G sites B
          (lpReplicaReflectedResidual G sites m.1 K.1)))

end
end StatMech.Ising
