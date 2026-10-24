/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_14.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Lemma_1_3
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open MeasureTheory Real ProbabilityTheory ENNReal Finset Set

noncomputable section
