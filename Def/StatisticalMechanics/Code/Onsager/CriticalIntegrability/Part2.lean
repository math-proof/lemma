/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalTransfer.Part2
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part2
open scoped Real
open MeasureTheory Interval


namespace StatMech.Onsager

noncomputable def ons_criticalInnerBound : ℝ :=
  |∫ k2 in (-Real.pi)..Real.pi, ons_criticalLogBound k2|

end StatMech.Onsager
