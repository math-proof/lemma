/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Set
import Def.v1.Atlas.TheoryOfComputation.code.SelfReference.Part2


namespace SelfReference

open TuringMachine

variable {Γ : Type}

/-- The data needed to build Sipser's self-reproducing TM SELF.
Bundles:
* an encoding `encode : TMDescription → List Γ`;
* the printer-machine constructor `printTM` together with its halting spec;
* a sequential `compose` operator that runs `A` then `B` (output of `A` becomes
  input of `B`) and whose code is some concatenation `combineDesc (encode A)
  (encode B)`;
* a "quine helper" `quineB` that on input `input` halts with
  `⟨P_input⟩ ⟨quineB⟩` on the tape.
This is exactly the structure used in the proof that some TM `SELF` prints its
own description on every input. -/
structure SelfRefFramework (Γ : Type) where
  encode : TMDescription Γ → List Γ
  printTM : List Γ → TMDescription Γ
  printTM_spec : ∀ (w input : List Γ), (printTM w).haltsWithOutput input w
  compose : TMDescription Γ → TMDescription Γ → TMDescription Γ
  compose_spec : ∀ (A B : TMDescription Γ) (w mid out : List Γ),
    A.haltsWithOutput w mid → B.haltsWithOutput mid out →
    (compose A B).haltsWithOutput w out
  combineDesc : List Γ → List Γ → List Γ
  encode_compose : ∀ (A B : TMDescription Γ),
    encode (compose A B) = combineDesc (encode A) (encode B)
  quineB : TMDescription Γ
  quineB_spec : ∀ (input : List Γ),
    quineB.haltsWithOutput input
      (combineDesc (encode (printTM input)) (encode quineB))

end SelfReference
