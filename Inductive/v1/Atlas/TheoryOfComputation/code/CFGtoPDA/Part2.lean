/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.ContextFree.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.ContextFree
import Def.v1.Atlas.TheoryOfComputation.code.CFGtoPDA.Part2
universe u_pda


namespace CFGtoPDA

open ContextFreeGrammar ContextFreeRule

variable {T : Type u_pda}

variable {g : ContextFreeGrammar T}

set_option maxRecDepth 1024 in


/-- `DerivesIn' g n γ δ` means `γ ⇒ⁿ δ` in `g`: there is a derivation of length exactly
`n` from `γ` to `δ` using the rules of `g`. -/
inductive DerivesIn' (g : ContextFreeGrammar T) :
    ℕ → List (Symbol T g.NT) → List (Symbol T g.NT) → Prop where
  | refl (γ) : DerivesIn' g 0 γ γ
  | step {n γ δ τ} : g.Produces γ δ → DerivesIn' g n δ τ → DerivesIn' g (n + 1) γ τ


/-- `StepCount M n c₁ c₂` means the PDA `M` reaches configuration `c₂` from `c₁` in
exactly `n` steps. This is the step-counted refinement of `M.Reaches`. -/
inductive StepCount (M : PDA T σ γ₁) :
    ℕ → PDA.Config (α := T) (σ := σ) (γ := γ₁) →
    PDA.Config (α := T) (σ := σ) (γ := γ₁) → Prop where
  | refl (c) : StepCount M 0 c c
  | step {n c1 c2 c3} : M.Step c1 c2 → StepCount M n c2 c3 → StepCount M (n + 1) c1 c3

end CFGtoPDA
