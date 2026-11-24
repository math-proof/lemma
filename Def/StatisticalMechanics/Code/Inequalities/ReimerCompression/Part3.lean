module
public import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
public import Mathlib.Combinatorics.SetFamily.Compression.Down
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part2
open MeasureTheory Finset
open scoped NNReal FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

open ConfigSpace

variable {E : Type*}


noncomputable def downCompress [Fintype E] [DecidableEq E] (i : E)
    (𝒜 : Finset (ConfigSpace E)) : Finset (ConfigSpace E) :=
  (Down.compression i (𝒜.image cfgSupport)).image supportCfg


end StatMech
