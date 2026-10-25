/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type} [Countable V] [DecidableEq V]

def PeriodicGraph.tailComponentVertices
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (K : Finset V)
    (D : (P.tailClusterGraph omega x).ComponentCompl
      (P.tailClusterCut omega x K)) : Set V :=
  Subtype.val '' (D : Set (P.TailClusterVertex omega x))

end StatMech.FK.PeriodicPlanar
