/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RecursionTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic

namespace RecursionTheorem

/-- Possible outcomes of running a Turing machine on an input: `accept` (enter
the accept state), `reject` (halt in the reject state) or `diverge` (run
forever). Matches the three TM outcomes described in Sipser's formal
definition. -/
inductive TMResult where
  | accept : TMResult
  | reject : TMResult
  | diverge : TMResult
  deriving DecidableEq

/-- An abstract acceptable indexing of Turing machines, stronger than the
language-level version used in `SelfReference.lean` because it records the full
*behavior* (`accept`/`reject`/`diverge`) of each machine on each input rather
than just the language. Provides the standard ingredients needed to prove the
Recursion Theorem: encoding/decoding, a pairing function, an `smn` function with
the usual specification, a notion of computable index transformations,
representability of computable transformations, and closure of `IsComputable`
under composition and the diagonal `x ↦ smn x x`. -/
structure TMCoding (Γ : Type) where
  TMIndex : Type
  encode : TMIndex → List Γ
  behavior : TMIndex → List Γ → TMResult
  decode : List Γ → Option TMIndex
  decode_encode : ∀ M : TMIndex, decode (encode M) = some M
  pair : List Γ → List Γ → List Γ
  pair_injective : ∀ a b c d, pair a b = pair c d → a = c ∧ b = d
  smn : TMIndex → TMIndex → TMIndex
  smn_spec : ∀ (e x : TMIndex) (w : List Γ),
    behavior (smn e x) w = behavior e (pair w (encode x))
  IsComputable : (TMIndex → TMIndex) → Prop
  representable : ∀ (h : TMIndex → TMIndex), IsComputable h →
    ∃ e : TMIndex, ∀ (x : TMIndex) (w : List Γ),
      behavior (smn e x) w = behavior (h x) w
  isComputable_smn_diag : IsComputable (fun x => smn x x)
  isComputable_comp : ∀ (f g : TMIndex → TMIndex),
    IsComputable f → IsComputable g → IsComputable (f ∘ g)
  isComputable_smn_apply : ∀ (e : TMIndex), IsComputable (smn e)

/-- The language of a TM index `M`: the set of inputs `w` on which `M` accepts. -/
def TMCoding.languageOf {Γ : Type} (C : TMCoding Γ) (M : C.TMIndex) : Set (List Γ) :=
  {w | C.behavior M w = TMResult.accept}
