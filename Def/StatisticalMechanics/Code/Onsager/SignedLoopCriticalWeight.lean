/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.CriticalPoint
import Theorem.StatisticalMechanics.Code.Ising.KramersWannier.Part2
import Mathlib.Analysis.SpecialFunctions.Artanh


namespace StatMech.Onsager

noncomputable def ons_signedLoopCriticalWeight : ℝ := Real.sqrt 2 - 1

end StatMech.Onsager
