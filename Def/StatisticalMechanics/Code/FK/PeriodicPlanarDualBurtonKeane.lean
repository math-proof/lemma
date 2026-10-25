/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneUniqueness
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualBurtonKeane
open MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


namespace PeriodicPlanarDualPair

def dualPatternPullback (D : PeriodicPlanarDualPair P Pdual)
    (I : Finset (Sym2 W)) (eta : ConfigSpace ↥I) :
    ConfigSpace ↥(I.map D.edgeDual.symm.toEmbedding) :=
  fun e => !eta ⟨D.edgeDual e.1, by simpa using e.2⟩


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
