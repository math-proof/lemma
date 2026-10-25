/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Lattice
import Def.v1.Atlas.TheoryOfComputation.code.ContextFree


namespace ChomskyNormalForm

variable {T : Type*}

/-- **Lemma 1 (Sipser, Lecture 7):** Every context free grammar can be converted
into an equivalent grammar in Chomsky Normal Form (i.e. one generating the same
language). -/
inductive DerivesIn (g : ContextFreeGrammar T) :
    List (Symbol T g.NT) → List (Symbol T g.NT) → ℕ → Prop where
  | refl (u : List (Symbol T g.NT)) : DerivesIn g u u 0
  | step {u v w : List (Symbol T g.NT)} {n : ℕ} :
      g.Produces u v → DerivesIn g v w n → DerivesIn g u w (n + 1)

end ChomskyNormalForm
