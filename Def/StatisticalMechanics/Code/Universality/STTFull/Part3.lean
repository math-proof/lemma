/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTFull.Part2
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

noncomputable def stt_coupling (p0 p1 p2 : ℝ) : Measure (LocalConfig × LocalConfig) :=
  ∑ ωt : LocalConfig, ∑ ωs : LocalConfig,
    (if stt_triConn ωt = stt_starConn ωs
      then stt_triW p0 p1 p2 ωt * stt_triW (1 - p0) (1 - p1) (1 - p2) ωs
            / stt_starMass (1 - p0) (1 - p1) (1 - p2) (stt_starConn ωs)
      else 0) • Measure.dirac (ωt, ωs)


end Universality
end StatMech
