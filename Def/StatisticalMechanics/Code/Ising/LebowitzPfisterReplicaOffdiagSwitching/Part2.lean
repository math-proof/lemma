/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCutParity.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagSeamSelector
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) (i j : I) (hij : i ≠ j)
    (n : Current (LPReplicaCurrentVertex V)) : I :=
  let H := lpReplicaCurrentGraph G sites
  let m := lpReplicaCurrentEdgeFlux G sites n
  let A := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  if h : StatMech.Sharpness.sources H (ofEdgeFun H m) = A then
    Classical.choose
      (lpReplicaCurrent_exists_positiveSeam_of_offdiagSource
        G sites hsite hij m h)
  else i


end
end StatMech.Ising
