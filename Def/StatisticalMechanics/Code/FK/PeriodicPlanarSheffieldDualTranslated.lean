/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldTransverseAssembly
open MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicGraph.translatedFiniteInfinitePairConnectionEvent
    (P : PeriodicGraph V) (z : Site 2) (L R : Finset V) (N : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  P.translateEvent z (P.finiteInfinitePairConnectionEvent L R N)

end StatMech.FK.PeriodicPlanar
