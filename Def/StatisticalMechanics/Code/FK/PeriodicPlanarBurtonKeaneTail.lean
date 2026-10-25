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
import Abbrev.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type} [Countable V] [DecidableEq V]

noncomputable def PeriodicGraph.tailClusterCut (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (x : V) (K : Finset V) :
    Finset (P.TailClusterVertex omega x) :=
  K.preimage Subtype.val Subtype.val_injective.injOn

end StatMech.FK.PeriodicPlanar
