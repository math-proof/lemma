/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

noncomputable def stt_triLocalMeasure (p0 p1 p2 : ℝ) : Measure LocalConfig :=
  ∑ ω : LocalConfig, ENNReal.ofReal (localWeight p0 p1 p2 ω) • Measure.dirac ω


def stt_triConn (ω : LocalConfig) : Bool × Bool × Bool := (triAB ω, triAC ω, triBC ω)


def stt_starConn (ω : LocalConfig) : Bool × Bool × Bool := (starAB ω, starAC ω, starBC ω)


end Universality
end StatMech
