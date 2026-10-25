/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part6
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

noncomputable def loewnerLifetime (W : ℝ → ℝ) (z : ℂ) : ENNReal :=
  ⨆ T : {T : ℝ // IsLoewnerAdmissibleDuration W z T}, ENNReal.ofReal T.1


end StatMech.SLE
