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
import Def.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part2
open MeasureTheory Finset
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {E : Type*}


@[simp] lemma cfgEquivFinset_apply [Fintype E] [DecidableEq E] (ω : ConfigSpace E) :
    cfgEquivFinset ω = cfgSupport ω := rfl

@[simp] lemma cfgEquivFinset_symm_apply [Fintype E] [DecidableEq E] (s : Finset E) :
    cfgEquivFinset.symm s = supportCfg s := rfl


end StatMech
