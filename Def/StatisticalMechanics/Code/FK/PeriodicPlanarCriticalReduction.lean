/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarThermodynamicDuality.Part2
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


def PeriodicGraph.openSubgraph (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := P.graph.Adj x y ∧ omega s(x, y) = true
  symm := ⟨fun x y h => ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨fun x h ↦ h.1.ne rfl⟩

end PeriodicPlanar
end FK
end StatMech
