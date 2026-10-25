/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part10
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

def loewnerUnswallowedDomain (W : ℝ → ℝ) (t : ℝ) : Set ℂ :=
  {z | z ∈ upperHalfPlane ∧ IsBeforeLoewnerLifetime W z t}


end StatMech.SLE
