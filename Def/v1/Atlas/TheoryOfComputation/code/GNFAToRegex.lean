/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TheoryOfComputation.code.GNFA
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.GNFA
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.RegularLanguages
import Def.v1.Atlas.TheoryOfComputation.code.RegularLanguages
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.DFA
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Option
open Language Set


namespace Sipser

/--
**The "rip" construction (state elimination).**

Given a GNFA `G` and a state `x` that is neither the start nor the accept
state, `G.rip x hxs hxa` is the GNFA on the states `{q // q ≠ x}` obtained
by removing `x` and, for every remaining pair of states `qᵢ, qⱼ`,
replacing the label `δ(qᵢ, qⱼ)` by the union

  `δ(qᵢ, qⱼ) ∪ δ(qᵢ, x) · δ(x, x)* · δ(x, qⱼ)`

so that every path that used to pass through `x` is now captured by a
direct arrow.  This is the inductive step of the proof that every GNFA
has an equivalent regular expression.
-/
noncomputable def GNFA.rip {Q : Type*} {σ : Type*} [Fintype Q] [DecidableEq Q]
    (G : GNFA Q σ) (x : Q) (hxs : x ≠ G.start) (hxa : x ≠ G.accept) :
    GNFA {q : Q // q ≠ x} σ where
  start := ⟨G.start, hxs.symm⟩
  accept := ⟨G.accept, hxa.symm⟩
  start_ne_accept := by intro h; exact G.start_ne_accept (Subtype.mk.inj h)
  δ qi qj :=
    if qj.val = G.start then RegularExpression.zero
    else if qi.val = G.accept then RegularExpression.zero
    else (G.δ qi.val qj.val).plus
           ((G.δ qi.val x).comp ((G.δ x x).star.comp (G.δ x qj.val)))
  no_enter_start _ := by simp
  no_exit_accept _ := by simp [G.start_ne_accept]

/-- The regular expression matching the *single-symbol* language
`{[a] | a ∈ l}` — a finite union of `char` regexes (or `zero` if the
list is empty). -/
def regexCharUnion {α : Type*} : List α → RegularExpression α
  | [] => RegularExpression.zero
  | a :: as => (RegularExpression.char a).plus (regexCharUnion as)

/-- For a DFA `M` and states `s, s'`, `dfaCharRegex M s s'` is the regular
expression matching exactly the single-letter words `[a]` for which
`M.step s a = s'`. -/
noncomputable def dfaCharRegex (M : DFA α σ) (s s' : σ) : RegularExpression α :=
  regexCharUnion ((Finset.univ.filter (fun a => M.step s a = s')).val.toList)

/--
**DFA → GNFA conversion.**

Given a DFA `M` with states `σ`, build an equivalent GNFA whose state
type is `Option (Option σ)`:

* the outer `none` is the new GNFA `start` state;
* `some none` is the new GNFA `accept` state;
* `some (some s)` corresponds to an original DFA state `s ∈ σ`.

Transitions are: an ε-edge from `start` to `some (some M.start)` (and
directly to the accept state when `M.start ∈ M.accept`), an ε-edge from
every DFA-accept state to the new accept state, and between two DFA
states `s, s'` the regex `dfaCharRegex M s s'`.  All other arrows are
`zero`, and the no-enter-start / no-exit-accept conditions hold by
construction.
-/
noncomputable def dfaToGNFA (M : DFA α σ) : GNFA (Option (Option σ)) α :=
  haveI : DecidablePred (· ∈ M.accept) := Classical.decPred _
  { start := none
    accept := some none
    start_ne_accept := nofun
    δ := fun qi qj => match qi, qj with
      | none, none => .zero
      | none, some none =>
          if M.start ∈ M.accept then .epsilon else .zero
      | none, some (some s) =>
          if s = M.start then .epsilon else .zero
      | some none, _ => .zero
      | some (some _), none => .zero
      | some (some s), some none =>
          if s ∈ M.accept then .epsilon else .zero
      | some (some s), some (some s') =>
          dfaCharRegex M s s'
    no_enter_start := fun qi => by rcases qi with _ | (_ | _) <;> rfl
    no_exit_accept := fun qj => by rcases qj with _ | (_ | _) <;> rfl }

end Sipser
