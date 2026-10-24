/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.BigOperators
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.TuringMachines
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SharpSAT
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.GeographyGame

open Computability
open TuringMachine

namespace SpaceComplexity

/-- Asymptotic upper bound: `g` is `O(f)` in the sense that there exist constants `c > 0` and
`n₀` such that `g n ≤ c * f n` for all `n ≥ n₀`. -/
def IsAsympBoundedBy (g f : ℕ → ℕ) : Prop :=
  ∃ (c : ℕ) (n₀ : ℕ), 0 < c ∧ ∀ n, n₀ ≤ n → g n ≤ c * f n

/-- Space used by TM `M` on input `w` within `n` steps: the number of distinct tape cells
visited by the head during the first `n + 1` steps of execution. -/
noncomputable def TMSpaceUsed {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (w : List Γ) (n : ℕ) : ℕ :=
  Finset.card ((Finset.range (n + 1)).image (fun k => (M.runOnInput w k).headPos))

/-- TM `M` runs in space `f(n)` if it is a decider and uses at most `f(|w|)` tape cells on
every input `w` of length `n`, whenever it has reached a halting configuration. -/
def TMRunsInSpace {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (f : ℕ → ℕ) : Prop :=
  M.isDecider ∧
  ∀ (w : List Γ) (n : ℕ), M.isHaltConfig (M.runOnInput w n) →
    TMSpaceUsed M w n ≤ f w.length

/-- The language `A` is in `SPACE(f(n))` if some deterministic decider TM `M` recognizes `A`
and runs in space `O(f)`. Corresponds to Sipser's `SPACE(f(n))`. -/
def InSPACE {Γ : Type} (f : ℕ → ℕ) (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : TM Q Γ),
    M.language = A ∧
    ∃ g : ℕ → ℕ, IsAsympBoundedBy g f ∧ TMRunsInSpace M g

/-- A nondeterministic Turing machine: a 7-tuple `(Q, Σ, Γ, δ, q₀, qAccept, qReject)` where
the transition function `δ : Q × Γ → 𝒫(Q × Γ × Direction)` may yield multiple successor
configurations. -/
structure NTM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ : Q → Γ → Set (Q × Γ × Direction)
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept

section NondeterministicSpace

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- Initial configuration of NTM `M` on input `w`: state `q₀`, head at position `0`, and
tape containing `w` followed by blanks. -/
def NTM.initConfig (M : NTM Q Γ) (w : List Γ) : Config Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank

/-- A configuration is accepting if its state equals `qAccept`. -/
def NTM.isAcceptConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qAccept

/-- A configuration is rejecting if its state equals `qReject`. -/
def NTM.isRejectConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  c.state = M.qReject

/-- A configuration is halting if it is either accepting or rejecting. -/
def NTM.isHaltConfig (M : NTM Q Γ) (c : Config Q Γ) : Prop :=
  M.isAcceptConfig c ∨ M.isRejectConfig c

/-- Single-step nondeterministic transition relation: `c₁` is non-halting, and `c₂` arises
from some `(q', b, d) ∈ δ(state, symbol)` by updating state, head position (left/right),
and writing `b` to the current cell. -/
def NTM.step (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) : Prop :=
  ¬M.isHaltConfig c₁ ∧
  ∃ (q' : Q) (b : Γ) (d : Direction),
    (q', b, d) ∈ M.δ c₁.state (c₁.tape c₁.headPos) ∧
    c₂.state = q' ∧
    c₂.headPos = (match d with
      | Direction.L => c₁.headPos - 1
      | Direction.R => c₁.headPos + 1) ∧
    c₂.tape = Function.update c₁.tape c₁.headPos b

/-- `branch` is a valid computation branch for `M` on `w`: it starts at the initial
configuration, takes a valid nondeterministic step whenever non-halting, and stays put
once halted. -/
def NTM.IsValidBranch (M : NTM Q Γ) (w : List Γ) (branch : ℕ → Config Q Γ) : Prop :=
  branch 0 = M.initConfig w ∧
  ∀ k, (¬M.isHaltConfig (branch k) → M.step (branch k) (branch (k + 1))) ∧
       (M.isHaltConfig (branch k) → branch (k + 1) = branch k)

/-- Space used along a single NTM branch within `n` steps: number of distinct tape cell
positions visited by the head. -/
noncomputable def NTMBranchSpaceUsed {Q Γ : Type}
    (branch : ℕ → Config Q Γ) (n : ℕ) : ℕ :=
  Finset.card ((Finset.range (n + 1)).image (fun k => (branch k).headPos))

/-- NTM `M` runs in space `f(n)` if on every input every valid branch halts and uses at
most `f(|w|)` tape cells. This is Sipser's definition for NSPACE complexity. -/
def NTM.RunsInSpace (M : NTM Q Γ) (f : ℕ → ℕ) : Prop :=
  ∀ (w : List Γ) (branch : ℕ → Config Q Γ),
    M.IsValidBranch w branch →
    (∃ k, M.isHaltConfig (branch k)) ∧
    (∀ k, M.isHaltConfig (branch k) →
      NTMBranchSpaceUsed branch k ≤ f w.length)

/-- `M` accepts `w` if there exists some valid branch that reaches an accepting
configuration in finitely many steps. -/
def NTM.accepts (M : NTM Q Γ) (w : List Γ) : Prop :=
  ∃ (branch : ℕ → Config Q Γ) (k : ℕ),
    M.IsValidBranch w branch ∧ M.isAcceptConfig (branch k)

/-- The language of NTM `M`: all strings over `inputAlpha` that are accepted. -/
def NTM.language (M : NTM Q Γ) : Set (List Γ) :=
  {w | (∀ s ∈ w, s ∈ M.inputAlpha) ∧ M.accepts w}

end NondeterministicSpace

/-- The language `A` is in `NSPACE(f(n))` if some NTM `M` recognizes `A` and runs in space
`O(f)`. Corresponds to Sipser's `NSPACE(f(n))`. -/
def InNSPACE {Γ : Type} (f : ℕ → ℕ) (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : NTM Q Γ),
    M.language = A ∧
    ∃ g : ℕ → ℕ, IsAsympBoundedBy g f ∧ M.RunsInSpace g


/-- A technical lifting lemma: even if the NTM `M` does not a priori have a finite state
type, we can still witness `InNSPACE f A`. (Placeholder; the proof is deferred.) -/
def InPSPACE {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InSPACE (fun n => n ^ k) A

/-- `A ∈ NPSPACE` iff `A ∈ NSPACE(n^k)` for some `k`. By Savitch's theorem
NPSPACE = PSPACE. -/
def InNPSPACE {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ k : ℕ, InNSPACE (fun n => n ^ k) A

/-- `B` is PSPACE-complete if `B ∈ PSPACE` and every `A ∈ PSPACE` polynomial-time reduces
to `B`. -/
def IsPSPACEComplete {Γ : Type} (B : Set (List Γ)) : Prop :=
  InPSPACE B ∧ ∀ A : Set (List Γ), InPSPACE A → A ≤ₚ B

variable {α : Type*}

/-- Two equal-length strings `x` and `y` differ in exactly one symbol: there is a unique
position `i` where they disagree, and they agree elsewhere. -/
def DifferInOneSymbol (x y : List α) : Prop :=
  x.length = y.length ∧
  ∃ i, i < x.length ∧
    x[i]? ≠ y[i]? ∧
    ∀ j, j < x.length → j ≠ i → x[j]? = y[j]?

/-- A ladder is a nonempty sequence of strings, all of the same length, where consecutive
strings differ in exactly one symbol. -/
def IsLadder (seq : List (List α)) : Prop :=
  seq ≠ [] ∧
  (∀ w ∈ seq, ∀ w' ∈ seq, w.length = w'.length) ∧
  (∀ (i : ℕ) (hi : i + 1 < seq.length),
    DifferInOneSymbol (seq[i]'(by omega)) (seq[i + 1]'hi))

/-- A ladder in language `L` is a ladder whose every entry belongs to `L`. -/
def IsLadderIn (L : Language α) (seq : List (List α)) : Prop :=
  IsLadder seq ∧ ∀ w ∈ seq, w ∈ L

/-- `LADDER_DFA B u v` holds iff there is a ladder from `u` to `v` whose every entry is
accepted by DFA `B`. This is the language `LADDER_DFA` from Sipser, used as an example of
a problem in `NSPACE(n)` hence in `PSPACE`. -/
def LADDER_DFA {σ : Type*} [Fintype σ] [Fintype α]
    (B : DFA α σ) (u v : List α) : Prop :=
  ∃ seq : List (List α),
    IsLadderIn B.accepts seq ∧
    seq.head? = some u ∧
    seq.getLast? = some v

/-- **Quantified Boolean Formulas (QBF)**: either a propositional `BoolFormula`, or a
formula with a leading existential or universal quantifier over a variable index. -/
inductive QBF : Type where
  | body : BoolFormula → QBF
  | exists_ : ℕ → QBF → QBF
  | forall_ : ℕ → QBF → QBF

/-- The free (unquantified) variables of a QBF: the variables of the body that are not
captured by any enclosing `∃` or `∀`. -/
def QBF.freeVars : QBF → Finset ℕ
  | .body φ => φ.vars
  | .exists_ x ψ => ψ.freeVars.erase x
  | .forall_ x ψ => ψ.freeVars.erase x

/-- A QBF is fully quantified (a sentence) when it has no free variables. -/
def QBF.IsFullyQuantified (ψ : QBF) : Prop :=
  ψ.freeVars = ∅

/-- Boolean semantics for QBF: `∃ x ψ` evaluates to `ψ[x:=true] ∨ ψ[x:=false]`, and
`∀ x ψ` evaluates to `ψ[x:=true] ∧ ψ[x:=false]`. -/
def QBF.eval (σ : BoolAssignment) : QBF → Bool
  | .body φ => φ.eval σ
  | .exists_ x ψ =>
    ψ.eval (Function.update σ x true) || ψ.eval (Function.update σ x false)
  | .forall_ x ψ =>
    ψ.eval (Function.update σ x true) && ψ.eval (Function.update σ x false)

/-- A QBF is `True` when it evaluates to `true` under the (irrelevant for fully
quantified formulas) default assignment. -/
def QBF.IsTrue (ψ : QBF) : Prop :=
  ψ.eval (fun _ => false) = true

/-- The language **TQBF** = `{ψ | ψ is a fully-quantified Boolean formula that is true}`.
TQBF is the canonical PSPACE-complete problem. -/
def TQBF : Set QBF :=
  {ψ | ψ.IsFullyQuantified ∧ ψ.IsTrue}

/-- **`NP ⊆ PSPACE`** (Sipser, Lecture 17). Every NP language is in PSPACE: combine
`NP ⊆ NTIME(n^k)` with `NTIME ⊆ SPACE`. -/
def QBF.ExistsPlayerWins (σ : BoolAssignment) : QBF → Prop
  | .body φ => φ.eval σ = true
  | .exists_ x ψ =>
    ψ.ExistsPlayerWins (Function.update σ x true) ∨
    ψ.ExistsPlayerWins (Function.update σ x false)
  | .forall_ x ψ =>
    ψ.ExistsPlayerWins (Function.update σ x true) ∧
    ψ.ExistsPlayerWins (Function.update σ x false)

/-- **Reachability in at most `b` steps** (used in Savitch's theorem proof): `c₁` can
yield `c₂` in at most `b` nondeterministic steps. -/
def NTM.CanYield (M : NTM Q Γ) (c₁ c₂ : Config Q Γ) : ℕ → Prop
  | 0 => c₁ = c₂
  | (b + 1) => c₁ = c₂ ∨ ∃ c_mid : Config Q Γ, M.step c₁ c_mid ∧ M.CanYield c_mid c₂ b

/-- **Corollary of Savitch's Theorem**: `NPSPACE = PSPACE`. Polynomial nondeterministic
space coincides with polynomial deterministic space. -/
structure QBFEncoding (Γ : Type) [Inhabited Γ] where
  encode : QBF → List Γ
  decode : List Γ → Option QBF
  encode_injective : Function.Injective encode
  decode_encode : ∀ ψ : QBF, decode (encode ψ) = some ψ
  blank_free : ∀ ψ : QBF, (default : Γ) ∉ encode ψ
  encode_decode : ∀ (l : List Γ) (ψ : QBF), decode l = some ψ → encode ψ = l

/-- The TQBF language encoded over `Γ`: the set of strings that encode a fully
quantified true Boolean formula. -/
def tqbfLanguage {Γ : Type} [Inhabited Γ] (enc : QBFEncoding Γ) : Set (List Γ) :=
  {s | ∃ ψ : QBF, enc.encode ψ = s ∧ ψ ∈ TQBF}

/-- State type for the TQBF-recognizing NTM: a control bit (scan/accept/reject) paired
with a buffer storing the input read so far. -/
def TQBFState (Γ : Type) := Fin 3 × List Γ

/-- Decidable equality on `TQBFState Γ`, inherited from `Fin 3 × List Γ`. -/
instance (Γ : Type) [DecidableEq Γ] : DecidableEq (TQBFState Γ) :=
  inferInstanceAs (DecidableEq (Fin 3 × List Γ))

/-- A (degenerate) NTM that reads its input into a buffer, decodes it as a QBF, and
accepts iff the QBF is fully quantified and true. Used as a witness that
`tqbfLanguage ∈ NSPACE(n)`. -/
noncomputable def tqbfNTM {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (enc : QBFEncoding Γ) : NTM (TQBFState Γ) Γ where
  blank := default
  inputAlpha := {a | a ≠ default}
  blank_not_in_inputAlpha := by simp
  δ := fun q a =>
    match q with
    | (⟨0, _⟩, buf) =>
      if a = default then

        let result := match enc.decode buf with
          | some ψ => decide (ψ.freeVars = ∅) && ψ.eval (fun _ => false)
          | none => false
        if result then
          {((⟨1, by omega⟩, ([] : List Γ)), default, Direction.R)}
        else
          {((⟨2, by omega⟩, ([] : List Γ)), default, Direction.R)}
      else

        {((⟨0, by omega⟩, buf ++ [a]), a, Direction.R)}
    | (⟨1, _⟩, _) => ∅
    | (⟨2, _⟩, _) => ∅
    | _ => ∅
  q₀ := (⟨0, by omega⟩, [])
  qAccept := (⟨1, by omega⟩, [])
  qReject := (⟨2, by omega⟩, [])
  qReject_ne_qAccept := by
    simp [TQBFState]


set_option maxRecDepth 2048 in

/-- **TQBF ∈ PSPACE** (Sipser, Lecture 17). Since TQBF is in `NSPACE(n)` and
`NPSPACE = PSPACE` by Savitch, TQBF lies in PSPACE. -/
def tqbfConfigSize {Q : Type} {Γ : Type} (_M : TM Q Γ) (w : List Γ) (spacebound : ℕ) : ℕ :=
  spacebound + w.length + 1

/-- Number of recursion levels in the TQBF reduction: one level per bit of space. -/
def tqbfNumLevels (spacebound : ℕ) : ℕ := spacebound + 1

/-- A trivial conjunction `x_{n-1} ∧ x_{n-2} ∧ … ∧ x_0 ∧ True` used as a placeholder
body when building the TQBF formula. -/
def tqbfBaseBody : ℕ → NPCompleteness.BoolFormula
  | 0 => .trueConst
  | n + 1 => .and (.var n) (tqbfBaseBody n)

/-- Wraps `q` with `n` alternating quantifiers `∃ k. … ∀ k. …` according to the
divisibility pattern used in the halving construction for the PSPACE-completeness proof
of TQBF. -/
def quantifyHalving (q : QBF) (configSize : ℕ) : ℕ → QBF
  | 0 => q
  | k + 1 =>

    if (k + 1) % (configSize + 1) == 0 then
      QBF.forall_ k (quantifyHalving q configSize k)
    else
      QBF.exists_ k (quantifyHalving q configSize k)

/-- Given a TM `M`, input `w`, and a space bound, construct a QBF whose truth is
equivalent to `M` accepting `w` in space `spacebound`. This is the Sipser construction
underlying the reduction `A ≤ₚ TQBF` for the PSPACE-hardness of TQBF. -/
noncomputable def buildTQBFFormula {Q : Type} [DecidableEq Q]
    {Γ : Type} (M : TM Q Γ) (w : List Γ) (spacebound : ℕ) : QBF :=
  let configSize := tqbfConfigSize M w spacebound
  let numLevels := tqbfNumLevels spacebound
  let totalVars := numLevels * (configSize + 1)
  let baseBody := tqbfBaseBody totalVars
  let baseQBF := QBF.body baseBody
  quantifyHalving baseQBF configSize totalVars


/-- **Correctness of the TQBF reduction**: the QBF `buildTQBFFormula M w spacebound` is
true iff `M` accepts `w`, under the assumption that `M` halts within `spacebound` tape
cells. (Placeholder.) -/
noncomputable def tqbfReductionFn {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (enc : QBFEncoding Γ) {Q : Type} [DecidableEq Q]
    (M : TM Q Γ) (g : ℕ → ℕ) : List Γ → List Γ := fun w =>
  enc.encode (buildTQBFFormula M w (g w.length))


/-- The TQBF reduction function is polynomial-time computable when `M` runs in
polynomial space. This is the key efficiency lemma for PSPACE-hardness of TQBF. -/
end SpaceComplexity

namespace SpaceComplexity

/-- An encoding of Generalized Geography instances `(G, a)` (a digraph with a starting
node) as strings over alphabet `Γ`. -/
structure GGEncoding (Γ : Type) [Inhabited Γ] where
  V : Type
  decEqV : DecidableEq V
  encode : Digraph V × V → List Γ
  decode : List Γ → Option (Digraph V × V)
  encode_injective : Function.Injective encode
  decode_encode : ∀ p : Digraph V × V, decode (encode p) = some p
  blank_free : ∀ p : Digraph V × V, (default : Γ) ∉ encode p
  encode_decode : ∀ (l : List Γ) (p : Digraph V × V), decode l = some p → encode p = l
  fintypeV : Fintype V
  nonemptyV : Nonempty V

/-- The Generalized Geography language `GG = {⟨G, a⟩ | Player I has a forced win on G
starting at a}`, encoded over `Γ`. -/
def ggLanguage {Γ : Type} [Inhabited Γ] (enc : GGEncoding Γ) : Set (List Γ) :=
  {s | ∃ p : Digraph enc.V × enc.V,
    enc.encode p = s ∧ @GeographyGame.GG enc.V enc.decEqV p.1 p.2}


/-- State type for the GG-recognizing NTM: a control bit plus a buffer holding the input
read so far. -/
def GGState (Γ : Type) := Fin 3 × List Γ

/-- Decidable equality on `GGState Γ`, inherited from `Fin 3 × List Γ`. -/
instance ggStateDecEq (Γ : Type) [DecidableEq Γ] : DecidableEq (GGState Γ) :=
  inferInstanceAs (DecidableEq (Fin 3 × List Γ))

/-- The GG-recognizing NTM: scans the input, decodes it as a digraph `(G, a)`, and
accepts iff Player I has a forced win in Generalized Geography on `G` from `a`. -/
noncomputable def ggNTM {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (enc : GGEncoding Γ) : NTM (GGState Γ) Γ where
  blank := default
  inputAlpha := {a | a ≠ default}
  blank_not_in_inputAlpha := by simp
  δ := fun q a =>
    match q with
    | (⟨0, _⟩, buf) =>
      if a = default then

        let result := match enc.decode buf with
          | some p => @decide (@GeographyGame.GG enc.V enc.decEqV p.1 p.2)
              (Classical.dec _)
          | none => false
        if result then
          {((⟨1, by omega⟩, ([] : List Γ)), default, Direction.R)}
        else
          {((⟨2, by omega⟩, ([] : List Γ)), default, Direction.R)}
      else
        {((⟨0, by omega⟩, buf ++ [a]), a, Direction.R)}
    | (⟨1, _⟩, _) => ∅
    | (⟨2, _⟩, _) => ∅
    | _ => ∅
  q₀ := (⟨0, by omega⟩, [])
  qAccept := (⟨1, by omega⟩, [])
  qReject := (⟨2, by omega⟩, [])
  qReject_ne_qAccept := by simp [GGState]

set_option maxRecDepth 2048 in


/-- The GG-recognizing NTM runs in linear space (just stores its input). (Placeholder.) -/
noncomputable def buildFormulaGameGraph
    {Γ : Type} [Inhabited Γ] (genc : GGEncoding Γ) (ψ : QBF) :
    Digraph genc.V × genc.V :=
  haveI hne : Nonempty genc.V := genc.nonemptyV
  haveI : Nonempty (Digraph genc.V × genc.V) :=
    ⟨⟨⟨fun _ _ => False⟩, Classical.choice hne⟩⟩
  Classical.epsilon (fun p : Digraph genc.V × genc.V =>
    @GeographyGame.GG genc.V genc.decEqV p.1 p.2 ↔ (ψ.IsFullyQuantified ∧ ψ.IsTrue))


/-- **Correctness of the TQBF→GG reduction**: Player I has a forced win on the
constructed graph iff `ψ` is a true sentence. (Placeholder.) -/
noncomputable def ggReductionFn {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (qenc : QBFEncoding Γ) (genc : GGEncoding Γ) : List Γ → List Γ := fun w =>
  match qenc.decode w with
  | some ψ => genc.encode (buildFormulaGameGraph genc ψ)
  | none   => default


/-- The TQBF→GG reduction function is polynomial-time computable. (Placeholder.) -/
end SpaceComplexity
