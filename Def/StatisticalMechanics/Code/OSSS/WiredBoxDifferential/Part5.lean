module
public import Theorem.StatisticalMechanics.Code.OSSS.ActiveBoundaryDifferential
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Instance.StatisticalMechanics.Code.OSSS.WiredBoxDifferential
open scoped BigOperators Classical
open Finset Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace OSSS

namespace WiredBoxDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open ActiveBoundaryDifferential

open FK RevealmentTranslation


noncomputable def wiredFullCrossMass (d n : Nat) (q beta : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 (boxVerts d n)),
    (FK.restrictActive (boxGraph d n) ⁻¹'
      crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n)).indicator
        (fun _ => (1 : Real)) omega *
      wiredFkProb (boxGraph d n) (boxBoundary d n)
        (1 - Real.exp (-beta)) q omega

end WiredBoxDifferential
end OSSS
end StatMech
