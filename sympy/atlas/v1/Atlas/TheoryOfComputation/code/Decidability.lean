/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Countable
import Mathlib.Computability.Language
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

import sympy.atlas.v1.Atlas.TheoryOfComputation.code.TuringMachines
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Reductions

namespace Decidability

/-- A set `s : Set α` is countable if it is finite or has the same size as `ℕ`. -/
def IsCountable {α : Type*} (s : Set α) : Prop := s.Countable

/-- A `TMDesc` packages a Turing machine together with its (decidable) state type and an input
string. This corresponds to the encoded pair `⟨M, w⟩` used throughout Sipser's undecidability
arguments — for example, the input to a putative decider for `A_TM`. -/
structure TuringMachine.TMDesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  tm : TuringMachine.TM Q Γ
  input : List Γ

namespace TuringMachine

variable {Γ : Type}

/-- `d.accepts` holds when the underlying TM `d.tm` accepts the input `d.input`. -/
def TMDesc.accepts (d : TMDesc Γ) : Prop :=
  @TM.accepts d.Q Γ d.decEq d.tm d.input

/-- `d.halts` holds when the underlying TM `d.tm` halts (accepts or rejects) on the input
`d.input`. -/
def TMDesc.halts (d : TMDesc Γ) : Prop :=
  @TM.halts d.Q Γ d.decEq d.tm d.input

/-- A `TMEncoding` over alphabet `Γ` is a bundle of all the encoding/universal-machine
machinery used informally in Sipser. It provides:
* an injective encoding `encode : TMDesc Γ → List Γ` with a decoder,
* a self-reference principle (used for the Recursion Theorem / diagonal argument),
* a universal TM `U` that simulates encoded TMs whenever they halt,
* sequential composition of a decider with another TM, and
* transducer composition with computable functions, as used in mapping reductions. -/
structure TuringMachine.TMEncoding (Γ : Type) where
  encode : TuringMachine.TMDesc Γ → List Γ
  decode : List Γ → Option (TuringMachine.TMDesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d
  selfRef : ∀ {Q₀ : Type} [DecidableEq Q₀] (M : TuringMachine.TM Q₀ Γ),
    ∃ d : TuringMachine.TMDesc Γ,
      d.accepts ↔ @TuringMachine.TM.accepts Q₀ Γ _ M (encode d)
  universalSim : ∃ (QU : Type) (_ : DecidableEq QU) (U : TuringMachine.TM QU Γ),
    (∀ d : TuringMachine.TMDesc Γ, d.halts →
      @TuringMachine.TM.halts QU Γ _ U (encode d)) ∧
    (∀ d : TuringMachine.TMDesc Γ, d.halts →
      (@TuringMachine.TM.accepts QU Γ _ U (encode d) ↔ d.accepts)) ∧
    (∀ s, @TuringMachine.TM.accepts QU Γ _ U s →
      ∃ d : TuringMachine.TMDesc Γ, encode d = s ∧ d.accepts)
  sequentialComposition : ∀ {QR QU : Type}
    [DecidableEq QR] [DecidableEq QU]
    (R : TuringMachine.TM QR Γ) (U : TuringMachine.TM QU Γ),
    R.isDecider →
    (∀ w, @TuringMachine.TM.accepts QR Γ _ R w →
      @TuringMachine.TM.halts QU Γ _ U w) →
    ∃ (QS : Type) (_ : DecidableEq QS) (S : TuringMachine.TM QS Γ),
      S.isDecider ∧
      (∀ w, @TuringMachine.TM.accepts QS Γ _ S w ↔
        (@TuringMachine.TM.accepts QR Γ _ R w ∧
         @TuringMachine.TM.accepts QU Γ _ U w))
  transducerComposition : ∀ (f : List Γ → List Γ),
    TuringMachine.IsComputableFunction f →
    ∀ {QR : Type} [DecidableEq QR] (R : TuringMachine.TM QR Γ),
    R.isDecider →
    ∃ (QS : Type) (_ : DecidableEq QS) (S : TuringMachine.TM QS Γ),
      S.isDecider ∧
      (∀ w, @TuringMachine.TM.accepts QS Γ _ S w ↔
        @TuringMachine.TM.accepts QR Γ _ R (f w))

namespace TuringMachine

/-- Dovetailing simulation. Given TMs `M₁`, `M₂` such that for every input `w` at least one of
them accepts, one can construct a decider `T` that simulates both in parallel and accepts iff
`M₁` accepts. This is the technical content behind Sipser's Lecture 8 theorem "If `A` and `Aᶜ`
are T-recognizable then `A` is decidable." -/
end TuringMachine

namespace TuringMachine

variable {Γ : Type}

/-- The acceptance problem for Turing machines: `A_TM = {⟨M, w⟩ | M accepts w}`.
The classical Sipser theorem says this language is undecidable but Turing-recognizable. -/
def A_TM (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDesc Γ, enc.encode d = s ∧ d.accepts}

/-- The halting problem: `HALT_TM = {⟨M, w⟩ | M halts on w}`, also undecidable. -/
def HALT_TM (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDesc Γ, enc.encode d = s ∧ d.halts}

/-- The "flipped" TM `H.flip` swaps the accept and reject states of `H`. If `H` is a decider
then `H.flip` decides the complement of `L(H)`. This is the standard construction used in the
diagonal proof that `A_TM` is undecidable. -/
def TuringMachine.TM.flip {Q : Type} (Γ : Type) [DecidableEq Q] (H : TuringMachine.TM Q Γ) :
    TuringMachine.TM Q Γ where
  blank := H.blank
  inputAlpha := H.inputAlpha
  blank_not_in_inputAlpha := H.blank_not_in_inputAlpha
  δ := H.δ
  q₀ := H.q₀
  qAccept := H.qReject
  qReject := H.qAccept
  qReject_ne_qAccept := H.qReject_ne_qAccept.symm

/-- The head movement directions `L` and `R` form a two-element `Fintype`. -/
instance : Fintype Direction where
  elems := {Direction.L, Direction.R}
  complete := fun x => by cases x <;> simp

/-- A language is "finitely Turing-decidable" if it is decided by some TM whose state set is
`Fin n` for some `n`. Up to renaming of states this is no weaker than `IsTuringDecidable`, but
restricting to `Fin n` makes the collection of such machines countable. -/
def IsTuringDecidableFinite {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ (n : ℕ) (M : TM (Fin n) Γ), M.isDecider ∧ M.language = A

/-- The raw data of a finite-state Turing machine over `Γ`: a state count `n`, a blank symbol,
a transition function, and start/accept/reject states. This is the carrier used to enumerate
TMs in a countable family. -/
abbrev TMDescType (Γ : Type) :=
  Σ n : ℕ, Γ × (Fin n → Γ → Fin n × Γ × Direction) × Fin n × Fin n × Fin n

/-- For finite alphabets, the set of finite-state TM descriptions is countable. -/
instance tmDescType_countable (Γ : Type) [Fintype Γ] [DecidableEq Γ] :
    Countable (TMDescType Γ) :=
  inferInstance

/-- Map a piece of raw TM data to its language. If `qAccept = qReject` (ill-formed data) the
language is empty; otherwise it is the language of the corresponding `TM`. -/
noncomputable def tmDescToLang (Γ : Type) [DecidableEq Γ] :
    TMDescType Γ → Set (List Γ) :=
  fun ⟨n, blank, δ, q₀, qAccept, qReject⟩ =>
    if h : qReject ≠ qAccept then
      (TM.mk blank ∅ (Set.notMem_empty _) δ q₀ qAccept qReject h : TM (Fin n) Γ).language
    else ∅

/-- A *domino* in the Post Correspondence Problem is a pair of strings (`top`, `bottom`) over
the alphabet `α`. -/
structure Domino (α : Type) where
  top : List α
  bottom : List α

/-- A *PCP instance* is a finite list of dominoes. -/
def PCPInstance (α : Type) := List (Domino α)

/-- A PCP instance `P` *has a match* if there is a nonempty sequence of indices `i₁, …, iₖ` such
that concatenating the tops in order produces the same string as concatenating the bottoms in
order. The PCP language is precisely the set of encoded instances with a match. -/
def hasMatch {α : Type} (P : PCPInstance α) : Prop :=
  ∃ (indices : List (Fin P.length)),
    indices ≠ [] ∧
    (indices.map (fun i => (P.get i).top)).flatten =
    (indices.map (fun i => (P.get i).bottom)).flatten

/-- An injective encoding/decoding scheme that turns PCP instances over `Γ` into strings
over `Γ`. -/
structure PCPEncoding (Γ : Type) where
  encode : PCPInstance Γ → List Γ
  decode : List Γ → Option (PCPInstance Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ P, decode (encode P) = some P

variable {Γ : Type}

/-- The Post Correspondence Problem language `PCP = {⟨P⟩ | P has a match}`. By Sipser's
Lecture 10 theorem, this language is undecidable. -/
def PCP (enc : PCPEncoding Γ) : Set (List Γ) :=
  {s | ∃ P : PCPInstance Γ, enc.encode P = s ∧ hasMatch P}

end PostCorrespondence

namespace LBADecidability

open TuringMachine

/-- An `LBADesc` packages a linearly bounded automaton (a finite-state TM constrained to its
input region) with an input string. Following Sipser, `LBA = ⟨B, w⟩` is the typical input to
`A_LBA`. -/
structure LBADesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  finQ : Fintype Q
  lba : @LBA Q Γ decEq
  input : List Γ

variable {Γ : Type}

/-- `d.accepts` holds when the LBA `d.lba` accepts the input string `d.input`. -/
def LBADesc.accepts (d : LBADesc Γ) : Prop :=
  @LBA.accepts d.Q Γ d.decEq d.lba d.input

/-- Injective encoding/decoding of `LBADesc`s into strings, used to formulate the language
`A_LBA`. -/
structure LBAEncoding (Γ : Type) where
  encode : LBADesc Γ → List Γ
  decode : List Γ → Option (LBADesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

/-- The acceptance language for LBAs: `A_LBA = {⟨B, w⟩ | LBA B accepts w}`. Sipser's Lecture 10
theorem shows this language is *decidable*. -/
def A_LBA (enc : LBAEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : LBADesc Γ, enc.encode d = s ∧ d.accepts}

/-- A *bounded configuration* records only the data of an LBA configuration that can vary in
the bounded simulation: state, head position in `Fin m`, and tape contents on the first `m`
cells. The total number of such configurations is finite. -/
def BoundedConfig (Q : Type) (Γ : Type) (m : ℕ) :=
  Q × Fin m × (Fin m → Γ)

/-- The set of bounded configurations of an LBA with state set `Q`, tape alphabet `Γ`, and
input bound `m` is finite when `Q` and `Γ` are. This finiteness is the basis of the decidability
of `A_LBA`: an LBA either accepts within `|Q| · m · |Γ|^m` steps or loops. -/
noncomputable instance instFintypeBoundedConfig (Q : Type) (Γ : Type) (m : ℕ)
    [Fintype Q] [DecidableEq Γ] [Fintype Γ] : Fintype (BoundedConfig Q Γ m) := by
  change Fintype (Q × Fin m × (Fin m → Γ))
  infer_instance

/-- Extract the bounded-configuration view of a TM configuration whose head lies in `[0, m)`. -/
def extractBoundedConfig {Q Γ : Type} (m : ℕ) (c : Config Q Γ)
    (h0 : 0 ≤ c.headPos) (h1 : c.headPos < ↑m) : BoundedConfig Q Γ m :=
  (c.state,
   ⟨c.headPos.toNat, by omega⟩,
   fun i => c.tape ↑i)

/-- Acceptance of an LBA description is decidable (classically). Constructively this follows
from the finiteness of LBA configurations, which bounds the search for an accepting run. -/
noncomputable instance lbaDesc_accepts_decidable
    (d : LBADesc Γ) : Decidable d.accepts := Classical.dec _


/-- There is a universal TM `U` that, when run on the encoding of an `LBADesc d`, simulates the
LBA `d.lba` on input `d.input` and decides whether it accepts. `U` always halts because LBAs
have only finitely many configurations on a fixed input, so non-acceptance can be detected by
pigeonhole. -/
end LBADecidability

namespace ELBA

open TuringMachine

/-- An `LBAMachineDesc` is an LBA on its own (no input attached), used for the emptiness
problem `E_LBA`. -/
structure LBAMachineDesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  finQ : Fintype Q
  lba : @LBA Q Γ decEq

variable {Γ : Type}

/-- The language accepted by an LBA description. -/
def LBAMachineDesc.language (d : LBAMachineDesc Γ) : Set (List Γ) :=
  @LBA.language d.Q Γ d.decEq d.lba

/-- Injective encoding/decoding of LBA machine descriptions, used to formulate `E_LBA`. -/
structure LBAMachineEncoding (Γ : Type) where
  encode : LBAMachineDesc Γ → List Γ
  decode : List Γ → Option (LBAMachineDesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

/-- The emptiness problem for LBAs: `E_LBA = {⟨B⟩ | L(B) = ∅}`. By Sipser's Lecture 10 theorem,
this language is undecidable. -/
def E_LBA (enc : LBAMachineEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : LBAMachineDesc Γ, enc.encode d = s ∧ d.language = ∅}

end ELBA


/-- Computation-history construction for `E_LBA`. Given a TM description `d`, one can build an
LBA `bd` whose language is empty iff `d` does *not* accept. (The LBA recognizes valid
accepting computation histories of `d`; emptiness corresponds to no accepting history existing,
i.e. `d` does not accept.) -/
namespace ELBA

open TuringMachine

/-- **Theorem (Sipser Lecture 10).** The LBA emptiness problem
`E_LBA = {⟨B⟩ | L(B) = ∅}` is undecidable. -/
end ELBA

/-- An injective encoding/decoding scheme that turns context-free grammars over `Γ` into
strings over `Γ`. Used to formulate `ALL_CFG`. -/
structure CFGEncoding (Γ : Type) where
  encode : ContextFreeGrammar Γ → List Γ
  decode : List Γ → Option (ContextFreeGrammar Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ g, decode (encode g) = some g


/-- **Computation-history reduction for `ALL_CFG`.** There is a computable function `f`
mapping TM encodings to CFG encodings such that, for any TM `d`, the CFG `f(⟨d⟩)` generates
*all* strings iff `d` does *not* accept (so the strings *not* generated correspond to
accepting computation histories of `d`), and on invalid inputs `f` outputs a universal CFG. -/
variable {Γ : Type}

/-- The universality problem for CFGs: `ALL_CFG = {⟨G⟩ | G is a CFG and L(G) = Σ*}`. By
Sipser's Lecture 10 theorem, this language is undecidable. -/
def ALL_CFG (enc : CFGEncoding Γ) : Set (List Γ) :=
  {s | ∃ g : ContextFreeGrammar Γ, enc.encode g = s ∧ g.language = Set.univ}

end AllCFG


/-- Re-export of the computation-history CFG construction at the top level. -/
namespace AllCFG

open TuringMachine

/-- **Theorem (Sipser Lecture 10).** `ALL_CFG = {⟨G⟩ | L(G) = Σ*}` is undecidable. -/
end AllCFG
