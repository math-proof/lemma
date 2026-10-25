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
import Def.v1.Atlas.TheoryOfComputation.code.SelfReference


namespace SelfReference

open TuringMachine

variable {Γ : Type}

/-- A `TMEncoding` packages the data Sipser uses to set up the self-reproducing
TM construction:
* `encode`  : turns a TM description into its string code `⟨M⟩`;
* `printTMDesc w` : the "printer" machine `P_w` that on any input halts with `w` on
  the tape (`printTMDesc_spec`);
* `q_computable` : the function `q(w) = ⟨P_w⟩` is computable.
This is the formal counterpart of the textbook Lemma giving the computable
function `q : Σ* → Σ*` with `q(w) = ⟨P_w⟩`. -/
structure TMEncoding (Γ : Type) where
  encode : TMDescription Γ → List Γ
  printTMDesc : List Γ → TMDescription Γ
  printTMDesc_spec : ∀ (w input : List Γ), (printTMDesc w).haltsWithOutput input w
  q_computable : TuringMachine.IsComputableFunction (fun w => encode (printTMDesc w))

end SelfReference
