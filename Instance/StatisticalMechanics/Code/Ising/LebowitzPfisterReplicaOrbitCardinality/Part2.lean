/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitGateFamily
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCardinality
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable instance instFintypeLPReplicaOrbitConfiguration
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaOrbitConfiguration G sites A B q) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  letI : Fintype {p : H.edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q} :=
    lpReplicaProfileOrbitFintype G sites q
  letI (m : {p : H.edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q}) :
      Fintype {a : H.edgeFinset -> Nat // a <= m.1} :=
    StatMech.Sharpness.instFintypeLe H m.1
  unfold LPReplicaOrbitConfiguration
  infer_instance


end
end StatMech.Ising
