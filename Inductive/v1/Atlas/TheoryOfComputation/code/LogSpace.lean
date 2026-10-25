/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Def.v1.Atlas.TheoryOfComputation.code.LogSpace.Part3
open SpaceComplexity
open TuringMachine


namespace LogSpace

/-- **Immerman–Szelepcsényi Theorem.** For any space bound `f` with
`f(n) ≥ log₂ n`, the class `NSPACE(f)` is closed under complementation:
if `A ∈ NSPACE(f)` then `Aᶜ ∈ NSPACE(f)`. -/
inductive BoundedReachable {V : Type*} (G : V → V → Prop) : ℕ → V → V → Prop where
  | refl (s : V) : BoundedReachable G 0 s s
  | step {d : ℕ} {s u t : V} : BoundedReachable G d s u → G u t →
      BoundedReachable G (d + 1) s t
  | weaken {d : ℕ} {s t : V} : BoundedReachable G d s t →
      BoundedReachable G (d + 1) s t

end LogSpace
