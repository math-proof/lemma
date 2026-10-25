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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part4


namespace StatMech

namespace Exact3D

namespace Ising3DTransitionAssemblyInputs

set_option linter.style.longLine false in


theorem transitionRegime
    (I : Ising3DTransitionAssemblyInputs) :
    Ising3DTransitionRegime :=
  Ising.ita_ising_transition 3 (by norm_num)
    I.isingBox I.thetaPc I.pc_lt_one

end Ising3DTransitionAssemblyInputs

set_option linter.style.longLine false in


theorem ising3D_transitionRegime_of_transitionAssemblyInputs
    (I : Ising3DTransitionAssemblyInputs) :
    Ising3DTransitionRegime :=
  I.transitionRegime

end Exact3D
end StatMech
