/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFLInterRegular.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.ContextFree.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.ContextFree
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.CFGtoPDA
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.RegularLanguages
import Inductive.v1.Atlas.TheoryOfComputation.code.CFGtoPDA.Part2
import Def.v1.Atlas.TheoryOfComputation.code.RegularLanguages
universe u


/-- Product construction of a PDA `P` and a DFA `D`. The resulting PDA has state set
`σ₁ × σ₂`; it simulates `P` on its first component and the DFA `D` on its second component.
For ε-transitions of `P`, the DFA state is left unchanged; for input transitions on `a`,
the DFA component advances by `D.step _ a`. This is the standard construction used to show
that the class of CFLs is closed under intersection with regular languages. -/
def product (P : PDA α σ₁ γ) (D : DFA α σ₂) : PDA α (σ₁ × σ₂) γ where
  step := fun ⟨qp, qd⟩ a pop =>
    match a with
    | none =>
      { ⟨(qp', qd), push⟩ | (qp' : σ₁) (push : Option γ)
          (_ : (qp', push) ∈ P.step qp none pop) }
    | some a =>
      { ⟨(qp', D.step qd a), push⟩ | (qp' : σ₁) (push : Option γ)
          (_ : (qp', push) ∈ P.step qp (some a) pop) }
  start := (P.start, D.start)
  accept := P.accept ×ˢ D.accept

