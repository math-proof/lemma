/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.BonamiTwoPoint
import Def.StatisticalMechanics.Code.Probability.PBiasedTwoPoint.Part3
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

theorem pbt_tensorisation_reduction : pbt_TensorisationTarget := by
  intro p hp0 hp1 q hq1 hq2 ⟨Hcore, Hcore'⟩ u v
  exact pbt_two_point_value_of_core (le_of_lt hp0) (le_of_lt hp1) hq1 hq2 Hcore Hcore' u v

end StatMech.Probability
