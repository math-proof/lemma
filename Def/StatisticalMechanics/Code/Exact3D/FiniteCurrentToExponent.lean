/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part2


namespace StatMech

namespace Exact3D

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


noncomputable def massBridge
    (I : FiniteCurrentActualScheduleProjectionInputs) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    I.thermodynamicLimit I.fixedInner I.simonFreeSum I.projection

set_option linter.style.longLine false in


noncomputable def correlationLengthBridge
    (I : FiniteCurrentActualScheduleProjectionInputs) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge I.massBridge

end FiniteCurrentActualScheduleProjectionInputs
end Exact3D
end StatMech
