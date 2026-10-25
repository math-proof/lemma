/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ActiveBoundaryDifferential
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxDifferential.Part4
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace WiredBoxDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open ActiveBoundaryDifferential

open FK RevealmentTranslation


noncomputable def wiredActiveTheta (d n : Nat) (q beta : Real) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
      (FK.betaParams (fun _ => 1) beta) q)
    (crossIndG (boxActiveEdge d n) 0 n)

noncomputable def wiredActiveDenom (d n : Nat) (q beta : Real) : Real :=
  4 * (osssBoxFinset d n).sup' (by
      exact ⟨0, origin_mem_osssBoxFinset d n⟩)
    (fun x => ∑ j ∈ Finset.range n,
      Lindeberg.mean
        (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
          (FK.betaParams (fun _ => 1) beta) q)
        (fun omega => if ConnectedToSet d
          (liftCfg (boxActiveEdge d n) omega) x (centeredBoundary x j)
          then (1 : Real) else 0)) / (n : Real)


end WiredBoxDifferential
end OSSS
end StatMech
