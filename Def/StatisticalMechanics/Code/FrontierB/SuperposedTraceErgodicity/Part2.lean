module
public import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
public import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
public import Instance.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity
open MeasureTheory Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open ConfigSpace StatMech.FK

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


def pairConfig (omega eta : ConfigSpace E) : ConfigSpace (E ⊕ E)
  | Sum.inl e => omega e
  | Sum.inr e => eta e

end StatMech.FrontierB
