/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory

open MeasureTheory InformationTheory Finset Real

noncomputable section

namespace FanoInequality

/-- Uniform mixture measure `M⁻¹ ∑_j P j` over `M` probability measures. -/
noncomputable def mixtureMeasure {Ω : Type*} [MeasurableSpace Ω] {M : ℕ}
    (P : Fin M → Measure Ω) : Measure Ω :=
  (M : ENNReal)⁻¹ • ∑ j : Fin M, P j
