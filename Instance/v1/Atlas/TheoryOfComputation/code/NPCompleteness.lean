/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Structure.v1.Atlas.TheoryOfComputation.code.Tableau
import Inductive.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part2


namespace CookLevin

open TuringMachine NPCompleteness

/-- `SATState` is a finite type. -/
instance : Fintype SATState :=
  ⟨⟨[SATState.start, SATState.goodHead, SATState.badHead,
    SATState.accept, SATState.reject], by decide⟩,
    fun x => by cases x <;> simp⟩

end CookLevin
