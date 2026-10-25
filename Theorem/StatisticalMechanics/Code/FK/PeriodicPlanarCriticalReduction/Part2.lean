/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarThermodynamicDuality.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part2
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


theorem PeriodicGraph.root_mem_fundamentalDomain (P : PeriodicGraph V) :
    P.root ∈ P.fundamentalDomain :=
  P.fundamentalDomain_nonempty.choose_spec


end PeriodicPlanar
end FK
end StatMech
