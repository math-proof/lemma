/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCutParity.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part2
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagDisconnSlice
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) (i j : I) (hij : i ≠ j)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real)
    (k : I) : Real :=
  let H := lpReplicaCurrentGraph G sites
  let A := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  gatedSourcePairSum H beta J A ∅ (fun n =>
    (lpReplicaOffdiagSeamSelector G sites hsite i j hij n = k ∧
      ¬ CurrentConnected H n lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧
    CurrentConnected H n
      (lpReplicaCurrentLeft sites k) (lpReplicaCurrentRight sites k))


end
end StatMech.Ising
