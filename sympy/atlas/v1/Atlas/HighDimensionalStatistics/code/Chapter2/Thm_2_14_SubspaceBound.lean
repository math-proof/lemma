/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_SubspaceBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Def_2_12
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter2.Def_2_12
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_19
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter2.Thm_2_14_Bridge
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_19
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_14_Bridge
import Mathlib

open Matrix Finset BigOperators Rigollet MeasureTheory

noncomputable section
