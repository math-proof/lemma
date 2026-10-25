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
import Def.v1.Atlas.TheoryOfComputation.code.SelfReference.Part3


namespace SelfReference

open TuringMachine

variable {Γ : Type}

/-- An extension of `SelfRefFramework` exposing a concrete second-stage machine
`machineB` whose halting spec is stated directly in terms of the framework's
function `q`, matching the textbook construction `B(input) = ⟨P_q(input)⟩
⟨machineB⟩`. -/
structure SelfRefFrameworkExt (Γ : Type) extends SelfRefFramework Γ where
  machineB : TMDescription Γ
  machineB_spec : ∀ (input : List Γ),
    machineB.haltsWithOutput input
      (combineDesc (toSelfRefFramework.q input) (toSelfRefFramework.encode machineB))

/-- A "tape-output" fixed-point witness: a TM `fixedTM` whose output on `input` is
`g input ⟨fixedTM⟩`. This packages the self-referential ability to depend on one's
own code at the tape level, parameterized by an external two-argument map `g`. -/
structure TapeOutputFixedPoint (encode : TMDescription Γ → List Γ) where
  g : List Γ → List Γ → List Γ
  fixedTM : TMDescription Γ
  fixedTM_spec : ∀ (input : List Γ),
    fixedTM.haltsWithOutput input (g input (encode fixedTM))

end SelfReference

namespace TuringMachine

open TuringMachine

/-- An abstract acceptable indexing ("coding") of Turing machines over alphabet `Γ`,
sufficient to formalize the Recursion / Fixed-point theorems and the MIN_TM
unrecognizability proof. It records:
* an index type `TMIndex` with an `encode`/`decode` pair and language assignment;
* a pairing function `pair` on strings;
* an `smn` function with the standard `s-m-n` specification;
* a notion `IsComputable` of computable index transformations, closed under the
  needed operations (composition, applying `smn`, and the diagonal `x ↦ smn x x`);
* `representable`: every computable `h : TMIndex → TMIndex` is "implemented" by
  some index `e₀`, i.e. `languageOf (smn e₀ x) = languageOf (h x)`;
* `languages_beyond_length`: arbitrarily long codes are needed to span all
  languages — there exist indices whose language differs from all shorter ones;
* `recognizable_enumSearch_computable`: a recognizable set of codes plus an
  enumeration witness `t` that strictly increases code-length yields a
  computable `t`. -/
structure TMCoding (Γ : Type) where
  TMIndex : Type
  encode : TMIndex → List Γ
  languageOf : TMIndex → Set (List Γ)
  decode : List Γ → Option TMIndex
  decode_encode : ∀ M : TMIndex, decode (encode M) = some M
  pair : List Γ → List Γ → List Γ
  pair_injective : ∀ a b c d, pair a b = pair c d → a = c ∧ b = d
  smn : TMIndex → TMIndex → TMIndex
  smn_spec : ∀ (e x : TMIndex) (w : List Γ),
    w ∈ languageOf (smn e x) ↔ (pair w (encode x)) ∈ languageOf e
  IsComputable : (TMIndex → TMIndex) → Prop
  representable : ∀ (h : TMIndex → TMIndex), IsComputable h →
    ∃ e : TMIndex, ∀ x : TMIndex,
      languageOf (smn e x) = languageOf (h x)
  isComputable_smn_diag : IsComputable (fun x => smn x x)
  isComputable_comp : ∀ (f g : TMIndex → TMIndex),
    IsComputable f → IsComputable g → IsComputable (f ∘ g)
  isComputable_smn_apply : ∀ (e : TMIndex), IsComputable (smn e)
  languages_beyond_length : ∀ n : ℕ, ∃ M : TMIndex,
    ∀ M' : TMIndex, (encode M').length < n → languageOf M' ≠ languageOf M
  recognizable_enumSearch_computable :
    ∀ (P : TMIndex → Prop),
      IsTuringRecognizable {s : List Γ | ∃ M : TMIndex, encode M = s ∧ P M} →
      ∀ (t : TMIndex → TMIndex),
        (∀ M, P (t M) ∧ (encode M).length < (encode (t M)).length) →
        IsComputable t

end TuringMachine
