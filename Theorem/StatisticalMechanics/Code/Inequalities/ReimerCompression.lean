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
import Def.StatisticalMechanics.Code.Inequalities.ReimerCompression
open MeasureTheory Finset
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {E : Type*}


@[simp] lemma mem_cfgSupport [Fintype E] [DecidableEq E] (ω : ConfigSpace E) (i : E) :
    i ∈ cfgSupport ω ↔ ω i = true := by
  simp only [cfgSupport, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] lemma supportCfg_apply [DecidableEq E] (s : Finset E) (i : E) :
    supportCfg s i = decide (i ∈ s) := rfl

lemma supportCfg_cfgSupport [Fintype E] [DecidableEq E] (ω : ConfigSpace E) :
    supportCfg (cfgSupport ω) = ω := by
  funext i
  simp only [supportCfg_apply, mem_cfgSupport]
  cases ω i <;> simp

lemma cfgSupport_supportCfg [Fintype E] [DecidableEq E] (s : Finset E) :
    cfgSupport (supportCfg s) = s := by
  ext i
  simp only [mem_cfgSupport, supportCfg_apply, decide_eq_true_eq]


end StatMech
