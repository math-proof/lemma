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
import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part6


namespace CookLevin

open TuringMachine NPCompleteness

/-- Concrete one-symbol encoding of a HAMPATH instance: number of vertices `n`,
the edge relation, and the source/target vertices `s, t ∈ Fin n`. -/
inductive HampathSymbol
  | mk (n : ℕ) (edges : Fin n → Fin n → Bool) (s t : Fin n) : HampathSymbol

end CookLevin
