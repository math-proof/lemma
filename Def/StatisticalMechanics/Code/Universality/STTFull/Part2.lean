/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Abbrev.StatisticalMechanics.Code.Universality.STTFull
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

noncomputable def stt_starMass (p0 p1 p2 : ℝ) (c : Bool × Bool × Bool) : ℝ≥0∞ :=
  ∑ ω : LocalConfig, if stt_starConn ω = c then stt_triW p0 p1 p2 ω else 0


noncomputable def stt_triMass (p0 p1 p2 : ℝ) (c : Bool × Bool × Bool) : ℝ≥0∞ :=
  ∑ ω : LocalConfig, if stt_triConn ω = c then stt_triW p0 p1 p2 ω else 0


end Universality
end StatMech
