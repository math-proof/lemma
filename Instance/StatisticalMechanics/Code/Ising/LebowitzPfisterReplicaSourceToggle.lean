/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSourceToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSeamCrossing
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGeneralSourceSwitching
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.FrontierA

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

instance (G : SimpleGraph V) (sites : I -> V)
    (u v : LPReplicaCurrentVertex V) :
    DecidablePred (fun n : Current (LPReplicaCurrentVertex V) =>
      CurrentConnected (lpReplicaCurrentGraph G sites) n u v) :=
  fun _ => Classical.propDecidable _

end
end StatMech.Ising
