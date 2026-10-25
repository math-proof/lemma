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
import Theorem.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part3


namespace CookLevin

open TuringMachine NPCompleteness

/-- A directed graph on vertex type `V`, given by an edge relation `edge : V → V → Prop`. -/
structure DiGraph (V : Type*) where
  edge : V → V → Prop

end CookLevin
