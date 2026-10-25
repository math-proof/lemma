/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part12
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarThermodynamicDuality
open MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {E F : Type*}


@[simp] theorem dualConfigEquiv_apply (edgeDual : E ≃ F)
    (omega : ConfigSpace E) (f : F) :
    dualConfigEquiv edgeDual omega f = !(omega (edgeDual.symm f)) := rfl

@[simp] theorem dualConfigEquiv_symm_apply (edgeDual : E ≃ F)
    (eta : ConfigSpace F) (e : E) :
    (dualConfigEquiv edgeDual).symm eta e = !(eta (edgeDual e)) := rfl

theorem continuous_dualConfigEquiv (edgeDual : E ≃ F) :
    Continuous (dualConfigEquiv edgeDual) := by
  refine continuous_pi fun f => ?_
  exact (continuous_of_discreteTopology (f := fun b : Bool => !b)).comp
    (continuous_apply (edgeDual.symm f))

theorem continuous_dualConfigEquiv_symm (edgeDual : E ≃ F) :
    Continuous (dualConfigEquiv edgeDual).symm := by
  refine continuous_pi fun e => ?_
  exact (continuous_of_discreteTopology (f := fun b : Bool => !b)).comp
    (continuous_apply (edgeDual e))


end PeriodicPlanar
end FK
end StatMech
