/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
open Complex Set Metric Filter Topology
open scoped NNReal


namespace StatMech.SLE

def loewnerStrip (δ : ℝ) : Set ℂ := {w : ℂ | δ ≤ w.im}

end StatMech.SLE
