/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part9
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

noncomputable def selectedLoewnerSolution {W : ℝ → ℝ} {z : ℂ} {t : ℝ}
    (ht : IsBeforeLoewnerLifetime W z t) :
    LoewnerForwardSolution W z (selectedLoewnerDuration ht) :=
  Classical.choice (selectedLoewnerDuration_spec ht).1.2


noncomputable def loewnerMaximalCurve (W : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  by
    classical
    exact if ht : IsBeforeLoewnerLifetime W z t then
      (selectedLoewnerSolution ht).curve t else z


end StatMech.SLE
