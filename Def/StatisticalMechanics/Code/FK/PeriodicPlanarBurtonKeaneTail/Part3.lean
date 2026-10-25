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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail.Part3
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type} [Countable V] [DecidableEq V]

noncomputable def PeriodicGraph.infiniteTailData
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (hinf : (P.cluster omega x).Infinite) (K : Finset V) (hxK : x ∈ K) :
    P.InfiniteTailData omega K x :=
  (P.infiniteCluster_has_open_exit omega x hinf K hxK).some

end StatMech.FK.PeriodicPlanar
