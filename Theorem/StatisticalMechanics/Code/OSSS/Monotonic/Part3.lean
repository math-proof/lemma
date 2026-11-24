module
public import Theorem.StatisticalMechanics.Code.Inequalities.FKG
public import Def.StatisticalMechanics.Code.OSSS.Monotonic.Part3
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] [DecidableEq E] in

lemma isIncreasing_openAt (e : E) : IsIncreasing (OpenAt (E := E) e) := by
  intro x y hxy hx
  simp only [OpenAt, Set.mem_setOf_eq] at *
  have h := hxy e
  rw [hx] at h
  exact le_antisymm le_top h


end OSSS.Monotonic
end StatMech
