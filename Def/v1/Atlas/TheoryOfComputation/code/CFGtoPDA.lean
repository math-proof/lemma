/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.ContextFree.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.ContextFree
universe u_pda


namespace CFGtoPDA

open ContextFreeGrammar ContextFreeRule

variable {T : Type u_pda}

/-- A language `A ⊆ Σ*` is PDA-recognizable if there exist state and stack alphabet types
together with a pushdown automaton `P = (Q, Σ, Γ, δ, q₀, F)` whose accepted language equals `A`. -/
def IsPDARecognizable (A : Language T) : Prop :=
  ∃ (σ : Type u_pda) (γ : Type u_pda) (P : PDA T σ γ), P.language = A

end CFGtoPDA
