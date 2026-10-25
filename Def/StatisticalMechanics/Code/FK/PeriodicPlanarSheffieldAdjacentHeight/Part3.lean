/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdjacentHeight.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

def PeriodicPlaneEmbedding.finiteAdjacentHeightJoinedVerticalEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (t : Int)
    (L U : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectBottomBoundaryVertices a b c d) ∩
    E.rectSideConnectionEvent a b (c + t) (d + t) (U : Set V)
      (E.rectTopBoundaryVertices a b (c + t) (d + t))) \
    E.rectanglePairMergeErrorUnion a b c (d + t) L U

end StatMech.FK.PeriodicPlanar
