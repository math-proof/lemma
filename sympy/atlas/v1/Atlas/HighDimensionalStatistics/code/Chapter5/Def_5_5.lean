/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Def_5_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Prod
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory

set_option maxHeartbeats 4800000

open InformationTheory MeasureTheory MeasureTheory.Measure

noncomputable section

namespace Rigollet.Chapter5

/-- Kullback–Leibler divergence (Definition 5.5):
`KL(P ‖ Q) = ∫ log(dP/dQ) dP` if `P ≪ Q`, else `+∞`. Wraps Mathlib's `klDiv`. -/
noncomputable def klDivergence {Omega : Type*} [MeasurableSpace Omega]
    (P Q : Measure Omega) : ENNReal :=
  klDiv P Q

section Prop_5_6
