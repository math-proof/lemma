/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaAggregateSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaAggregateSwitching
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagToggledMass
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real)
    (i j : I) : Real :=
  let H := lpReplicaCurrentGraph G sites
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let A := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ T
  if hij : i = j then 0 else
    ∑ k : I, gatedSourcePairSum H beta J
      (A ∆ lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
      (fun n =>
        (lpReplicaOffdiagSeamSelector G sites hsite i j hij n = k ∧
          ¬ CurrentConnected H n
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧
        CurrentConnected H n
          (lpReplicaCurrentLeft sites k) (lpReplicaCurrentRight sites k))


end
end StatMech.Ising
