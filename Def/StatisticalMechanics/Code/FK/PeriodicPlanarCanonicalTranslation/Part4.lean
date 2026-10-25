/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

noncomputable def PeriodicGraph.shiftedToBufferedIncl
    (P : PeriodicGraph V) (z : Site 2) (n m : Nat)
    (hsub : (P.shiftedBufferedVertices z n : Set V) ⊆
      (P.orbitBox (P.bufferedRadius m) : Set V)) :
    P.ShiftedBufferedVertex z n → P.BufferedVertex m :=
  fun x => ⟨x.1, hsub x.2⟩

noncomputable def PeriodicGraph.bufferedToShiftedIncl
    (P : PeriodicGraph V) (z : Site 2) (n m : Nat)
    (hsub : (P.orbitBox (P.bufferedRadius n) : Set V) ⊆
      (P.shiftedBufferedVertices z m : Set V)) :
    P.BufferedVertex n → P.ShiftedBufferedVertex z m :=
  fun x => ⟨x.1, hsub x.2⟩

end StatMech.FK.PeriodicPlanar
