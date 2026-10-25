/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression
open MeasureTheory Finset
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {E : Type*}


def cfgEquivFinset [Fintype E] [DecidableEq E] : ConfigSpace E ≃ Finset E where
  toFun := cfgSupport
  invFun := supportCfg
  left_inv := supportCfg_cfgSupport
  right_inv := cfgSupport_supportCfg

end StatMech
