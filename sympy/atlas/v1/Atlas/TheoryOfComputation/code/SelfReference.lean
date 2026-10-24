/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Reductions
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Decidability
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Set

namespace SelfReference

open TuringMachine

/-- A self-contained description of a Turing machine over the tape alphabet `Γ`.
Bundles the (existential) state type `Q`, its `DecidableEq` instance, the underlying
`TM`, and an optional explicit source/encoding `source : List Γ` used by certain
concrete encodings. -/
structure TMDescription (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  machine : TM Q Γ
  source : List Γ := []

/-- The language `L(d)` recognized by the Turing machine packaged inside `d`. -/
def TMDescription.lang {Γ : Type} (d : TMDescription Γ) : Set (List Γ) :=
  @TM.language d.Q Γ d.decEq d.machine

variable {Γ : Type}

/-- `M.haltsWithOutput w out` says that running `M.machine` on input `w` reaches a
halt configuration after some number of steps `n`, and at that point the first
`out.length` cells of the tape spell out `out`. This is the "halt with `out` on the
tape" predicate used to formalize the printing/output behavior of TMs. -/
def TMDescription.haltsWithOutput (M : TMDescription Γ) (w out : List Γ) : Prop :=
  letI := M.decEq
  ∃ n : ℕ,
    M.machine.isHaltConfig (M.machine.runOnInput w n) ∧
    Config.readTape (M.machine.runOnInput w n) out.length = out

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

/-- `IsMinimalTM enc d` says `d` is a *minimal* Turing machine for its language under
the encoding `enc`: no strictly shorter description `d'` recognizes the same
language. Formally, for every `d'`, `|⟨d'⟩| < |⟨d⟩|` implies `L(d') ≠ L(d)`. -/
def IsMinimalTM {Γ : Type} (enc : TMEncoding Γ) (d : TMDescription Γ) : Prop :=
  ∀ d' : TMDescription Γ,
    (enc.encode d').length < (enc.encode d).length → d'.lang ≠ d.lang

/-- `MIN_TM = {⟨M⟩ | M is a minimal TM}`: the set of codes of minimal Turing
machines under the encoding `enc`. This is the language whose
Turing-unrecognizability is shown via the Recursion Theorem. -/
def MIN_TM {Γ : Type} (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDescription Γ, enc.encode d = s ∧ IsMinimalTM enc d}

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

/-- The computable map `q(w) := ⟨P_w⟩` inside a `SelfRefFramework`: it sends a
string `w` to the code of the printer-machine that outputs `w`. -/
def SelfRefFramework.q (F : SelfRefFramework Γ) (w : List Γ) : List Γ :=
  F.encode (F.printTM w)

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

/-- `PrintsAndHalts M w` says: started on the empty tape, `M` reaches an accept
configuration after some `n` steps, with cells `0, …, |w|-1` holding the symbols
of `w` and everywhere else the blank symbol. Captures "M halts having printed
exactly `w`". -/
def PrintsAndHalts {Q : Type} [DecidableEq Q] (M : TM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ,
    M.isAcceptConfig (M.runOnInput [] n) ∧
    (∀ (j : ℕ) (hj : j < w.length),
      (M.runOnInput [] n).tape (j : ℤ) = w[j]'hj) ∧
    (∀ i : ℤ, (i < 0 ∨ (w.length : ℤ) ≤ i) →
      (M.runOnInput [] n).tape i = M.blank)

/-- Same as `PrintsAndHalts` but starting from an arbitrary `input` instead of
the blank tape: after some `n` steps `M` accepts and the first `|w|` tape cells
contain `w`. -/
def PrintsAndHaltsOnInput {Q : Type} [DecidableEq Q] (M : TM Q Γ)
    (input w : List Γ) : Prop :=
  ∃ n : ℕ,
    M.isAcceptConfig (M.runOnInput input n) ∧
    (∀ (j : ℕ) (hj : j < w.length),
      (M.runOnInput input n).tape (j : ℤ) = w[j]'hj)

/-- The concrete *printer-machine* `P_w` for a string `w`: a TM with `|w| + 2`
states (one per character, plus an accept and a reject state) that on any input
writes `w[0], w[1], …, w[|w|-1]` left-to-right and accepts. This is the explicit
construction underlying the computable function `q(w) = ⟨P_w⟩`. -/
noncomputable def printTM (blank : Γ) (inputAlpha : Set Γ) (h_blank : blank ∉ inputAlpha)
    (w : List Γ) : TM (Fin (w.length + 2)) Γ where
  blank := blank
  inputAlpha := inputAlpha
  blank_not_in_inputAlpha := h_blank
  δ := fun q _ =>
    if hq : q.val < w.length then
      (⟨q.val + 1, by omega⟩, w[q.val]'hq, Direction.R)
    else (q, blank, Direction.R)
  q₀ := ⟨0, by omega⟩
  qAccept := ⟨w.length, by omega⟩
  qReject := ⟨w.length + 1, by omega⟩
  qReject_ne_qAccept := by simp

set_option maxHeartbeats 3200000 in
set_option linter.unusedSectionVars false in
/-- Key loop invariant of `printTM`: after `k ≤ |w|` steps on any `input`, the
machine is in state `k`, the head is at position `k`, and tape cells
`0, …, k-1` already hold the first `k` symbols of `w`. Proved by induction on
`k`. -/
theorem printTM_invariant_any_input (blank : Γ) (inputAlpha : Set Γ)
    (h_blank : blank ∉ inputAlpha) (w : List Γ) (input : List Γ)
    (k : ℕ) (hk : k ≤ w.length) :
    ((printTM blank inputAlpha h_blank w).runOnInput input k).state = ⟨k, by omega⟩ ∧
    ((printTM blank inputAlpha h_blank w).runOnInput input k).headPos = (k : ℤ) ∧
    (∀ (j : ℕ) (hj : j < k),
      ((printTM blank inputAlpha h_blank w).runOnInput input k).tape (j : ℤ) =
        w[j]'(by omega)) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, fun j hj => absurd hj (by omega)⟩
    · simp [TM.runOnInput, TM.run, TM.initConfig, printTM]
    · simp [TM.runOnInput, TM.run, TM.initConfig, printTM]
  | succ k ih =>
    have hk' : k ≤ w.length := by omega
    obtain ⟨hstate, hhead, htape_w⟩ := ih hk'
    have hk_lt : k < w.length := by omega
    set ck := (printTM blank inputAlpha h_blank w).runOnInput input k with hck_def
    have hrun_succ : (printTM blank inputAlpha h_blank w).runOnInput input (k + 1) =
        (printTM blank inputAlpha h_blank w).step ck := by
      simp [TM.runOnInput, TM.run, hck_def]
    have h_not_halt : ¬(ck.state = (printTM blank inputAlpha h_blank w).qAccept ∨
        ck.state = (printTM blank inputAlpha h_blank w).qReject) := by
      simp only [hstate, printTM, Fin.mk.injEq]; omega
    have hstep_def : (printTM blank inputAlpha h_blank w).step ck =
        ⟨⟨k + 1, by omega⟩, (k : ℤ) + 1, Function.update ck.tape (k : ℤ) (w[k]'hk_lt)⟩ := by
      unfold TM.step
      simp only [h_not_halt, ite_false]
      simp only [printTM, hstate, dif_pos hk_lt, hhead]
    rw [hrun_succ, hstep_def]
    refine ⟨rfl, ?_, ?_⟩
    · norm_cast
    · intro j hj
      simp only [Function.update]
      split_ifs with heq
      · have : j = k := by omega
        subst this; rfl
      · exact htape_w j (by omega)

set_option maxHeartbeats 800000 in
/-- Correctness of `printTM`: on any input, after exactly `|w|` steps the printer
machine `P_w` halts (in fact accepts) and the first `|w|` tape cells (read off by
`Config.readTape`) spell out `w`. This realizes the `haltsWithOutput` spec
demanded by `TMEncoding`. -/
theorem printTM_haltsWithOutput (blank : Γ) (inputAlpha : Set Γ)
    (h_blank : blank ∉ inputAlpha) (w input : List Γ) :
    ∃ n : ℕ,
      (printTM blank inputAlpha h_blank w).isHaltConfig
        ((printTM blank inputAlpha h_blank w).runOnInput input n) ∧
      Config.readTape ((printTM blank inputAlpha h_blank w).runOnInput input n) w.length = w := by
  have hinv := printTM_invariant_any_input blank inputAlpha h_blank w input w.length le_rfl
  refine ⟨w.length, ?_, ?_⟩
  ·
    left
    simp only [TM.isAcceptConfig, printTM]
    exact hinv.1
  ·
    simp only [Config.readTape]
    have hlen : (List.range w.length).length = w.length := List.length_range
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.length_map, List.length_range] at hi1
      simp only [List.getElem_map, List.getElem_range]
      exact hinv.2.2 i hi1

/-- A concrete instance of `TMEncoding` built from the explicit `printTM`
construction. The encoding of a description is taken to be its stored `source`
field, and `printTMDesc w` packages the `printTM w` machine together with
`source := w`, so `q(w) = encode(printTMDesc w) = w` is the identity, which is
clearly computable. -/
noncomputable def concreteTMEncoding (blank : Γ) (inputAlpha : Set Γ)
    (h_blank : blank ∉ inputAlpha) : SelfReference.TMEncoding Γ where
  encode := fun desc => desc.source
  printTMDesc := fun w =>
    { Q := Fin (w.length + 2)
      decEq := inferInstance
      machine := printTM blank inputAlpha h_blank w
      source := w }
  printTMDesc_spec := fun w input => by
    simp only [SelfReference.TMDescription.haltsWithOutput]
    exact printTM_haltsWithOutput blank inputAlpha h_blank w input
  q_computable := by


    show IsComputableFunction (fun w => w)
    refine ⟨Fin 2, inferInstance, {
      blank := blank
      inputAlpha := inputAlpha
      blank_not_in_inputAlpha := h_blank
      δ := fun _ a => (⟨0, by omega⟩, a, Direction.R)
      q₀ := ⟨0, by omega⟩
      qAccept := ⟨0, by omega⟩
      qReject := ⟨1, by omega⟩
      qReject_ne_qAccept := by simp
    }, fun w => ?_⟩


    refine ⟨0, ?_, ?_⟩
    ·
      left
      simp [TM.runOnInput, TM.run, TM.initConfig, TM.isAcceptConfig]
    ·
      simp only [TM.runOnInput, TM.run, TM.initConfig, Config.readTape]
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.length_map, List.length_range] at hi1
        simp only [List.getElem_map, List.getElem_range]
        have h_cond : (0 : ℤ) ≤ ((i : ℕ) : ℤ) ∧ ((i : ℕ) : ℤ) < (w.length : ℤ) := by
          constructor <;> omega
        rw [dif_pos h_cond]
        simp [Int.toNat_natCast]

set_option linter.unusedSectionVars false in

/-- Minimality in the `TMCoding` setting: `M` is minimal if no strictly
shorter-coded index `M'` has the same language. -/
def IsMinimalIndex (C : TMCoding Γ) (M : C.TMIndex) : Prop :=
  ∀ M' : C.TMIndex,
    (C.encode M').length < (C.encode M).length → C.languageOf M' ≠ C.languageOf M

/-- `MIN_TM = {⟨M⟩ | M is a minimal TM}` expressed in the `TMCoding` framework. -/
def MIN_TM_Coding (C : TMCoding Γ) : Set (List Γ) :=
  {s | ∃ M : C.TMIndex, C.encode M = s ∧ IsMinimalIndex C M}

/-- A `TMCoding` augmented with a computable "complement" operation `compl`
mapping each index `M` to an index whose language is the set complement of
`L(M)`. Useful for applying the Recursion Theorem to constructions that flip
acceptance. -/
structure TMCodingWithCompl (Γ : Type) where
  coding : TMCoding Γ
  compl : coding.TMIndex → coding.TMIndex
  compl_spec : ∀ M : coding.TMIndex, coding.languageOf (compl M) = (coding.languageOf M)ᶜ
  compl_computable : coding.IsComputable compl

/-- The complement `\overline{A_{TM}}` of the acceptance language `A_TM`. This
language is famously *not* Turing-recognizable and is the one whose
"unprovability" gives Gödel-style results in this development. -/
def A_TM_complement (enc : TMEncoding Γ) : Set (List Γ) :=
  (A_TM enc)ᶜ

/-- A minimal abstract "formal proof system" over a TM-encoding `enc`. It picks
out a Turing-recognizable set `provable ⊆ Σ*` of provable statements about TM
descriptions, with the soundness assumption that if `⟨d⟩ ∈ provable` then `d`
does *not* accept (the statement "`d` is non-accepting" is true). -/
structure FormalProofSystem (Γ : Type) where
  enc : TMEncoding Γ
  provable : Set (List Γ)
  sound : ∀ (d : TMDesc Γ), enc.encode d ∈ provable → ¬d.accepts
  provable_recognizable : IsTuringRecognizable provable

/-- A `FormalProofSystem` is *complete* if every true non-acceptance statement
is provable: whenever `d` does not accept, `⟨d⟩ ∈ provable`. Gödel's
First Incompleteness Theorem says no sound, recognizable system can be complete
in this sense. -/
def FormalProofSystem.isComplete {Γ : Type} (F : FormalProofSystem Γ) : Prop :=
  ∀ (d : TMDesc Γ), ¬d.accepts → F.enc.encode d ∈ F.provable
