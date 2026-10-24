/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Tableau
namespace NPCompleteness

/--
Syntax of propositional Boolean formulas over variables indexed by ℕ.
A `BoolFormula` is built from variables, the constants `true` and `false`,
and the connectives ¬, ∧, ∨.
-/
inductive BoolFormula : Type where
  | var : ℕ → BoolFormula
  | trueConst : BoolFormula
  | falseConst : BoolFormula
  | not : BoolFormula → BoolFormula
  | and : BoolFormula → BoolFormula → BoolFormula
  | or : BoolFormula → BoolFormula → BoolFormula
  deriving DecidableEq, Repr

/-- A truth assignment is a function from variable indices ℕ to `Bool`. -/
abbrev BoolAssignment := ℕ → Bool

/--
Evaluation of a Boolean formula under an assignment σ : ℕ → Bool.
Returns the standard truth value of the formula under σ.
-/
def BoolFormula.eval (σ : BoolAssignment) : BoolFormula → Bool
  | .var n => σ n
  | .trueConst => true
  | .falseConst => false
  | .not φ => !φ.eval σ
  | .and φ ψ => φ.eval σ && ψ.eval σ
  | .or φ ψ => φ.eval σ || ψ.eval σ

/-- A formula φ is *satisfiable* if there exists an assignment σ with `φ.eval σ = true`. -/
def BoolFormula.Satisfiable (φ : BoolFormula) : Prop :=
  ∃ σ : BoolAssignment, φ.eval σ = true

/-- `SAT = {φ | φ is a satisfiable Boolean formula}`. -/
def SAT : Set BoolFormula :=
  {φ | φ.Satisfiable}

/-- A *literal* is a variable or the negation of a variable. -/
def BoolFormula.IsLiteral : BoolFormula → Prop
  | .var _ => True
  | .not (.var _) => True
  | _ => False

/-- A *clause* is a disjunction of literals: either a single literal, or `l ∨ (rest)`
where `rest` is itself a clause. -/
def BoolFormula.IsClause : BoolFormula → Prop
  | .or φ ψ => φ.IsLiteral ∧ ψ.IsClause
  | φ => φ.IsLiteral

/-- A formula is in *Conjunctive Normal Form* (CNF) if it is a conjunction of clauses. -/
def BoolFormula.IsCNF : BoolFormula → Prop
  | .and φ ψ => φ.IsClause ∧ ψ.IsCNF
  | φ => φ.IsClause

/-- The length (number of literals) of a clause, counted by walking through the `or`s. -/
def BoolFormula.clauseLength : BoolFormula → ℕ
  | .or _ ψ => 1 + ψ.clauseLength
  | _ => 1

/-- A *3-clause* is a clause containing exactly 3 literals. -/
def BoolFormula.Is3Clause (φ : BoolFormula) : Prop :=
  φ.IsClause ∧ φ.clauseLength = 3

/-- A formula is in *3CNF* if it is a conjunction of 3-clauses. -/
def BoolFormula.Is3CNF : BoolFormula → Prop
  | .and φ ψ => φ.Is3Clause ∧ ψ.Is3CNF
  | φ => φ.Is3Clause

/-- `3SAT = {φ | φ is a satisfiable 3CNF formula}`. -/
def ThreeSAT : Set BoolFormula :=
  {φ | φ.Is3CNF ∧ φ.Satisfiable}

/-- Membership in `ThreeSAT` from the conjunction of being 3CNF and being satisfiable. -/
theorem ThreeSAT.mk {φ : BoolFormula} (h3 : φ.Is3CNF) (hsat : φ.Satisfiable) :
    φ ∈ ThreeSAT :=
  ⟨h3, hsat⟩

example : (BoolFormula.or (.var 0) (.or (.var 1) (.var 2))).Is3Clause := by
  constructor
  · exact ⟨trivial, ⟨trivial, trivial⟩⟩
  · rfl

example : (BoolFormula.or (.var 0) (.or (.var 1) (.var 2))).Is3CNF := by
  constructor
  · exact ⟨trivial, ⟨trivial, trivial⟩⟩
  · rfl

example : (BoolFormula.or (.var 0) (.or (.var 1) (.var 2))) ∈ ThreeSAT := by
  refine ⟨?_, ?_⟩
  · exact ⟨⟨trivial, ⟨trivial, trivial⟩⟩, rfl⟩
  · exact ⟨fun _ => true, rfl⟩

end NPCompleteness

open TuringMachine in
/--
A language `B` is **NP-hard** if every `A ∈ NP` is polynomial-time reducible to `B`,
i.e. for all `A ∈ NP`, `A ≤_P B`.
-/
def IsNPHard {Γ : Type} (B : Set (List Γ)) : Prop :=
  ∀ A : Set (List Γ), InNP A → PolyReducible A B

open TuringMachine in
/--
A language `B` is **NP-complete** if (1) `B ∈ NP` and (2) `B` is NP-hard, i.e.
for every `A ∈ NP`, `A ≤_P B`.
-/
def IsNPComplete {Γ : Type} (B : Set (List Γ)) : Prop :=
  InNP B ∧ (∀ A : Set (List Γ), InNP A → PolyReducible A B)

/-- The SAT language presented as a language of one-symbol input words `[φ]`
where the singleton list contains a satisfiable Boolean formula. -/
def SATLang : Set (List NPCompleteness.BoolFormula) :=
  {w | ∃ φ : NPCompleteness.BoolFormula, w = [φ] ∧ φ.Satisfiable}

namespace CookLevin

open TuringMachine NPCompleteness

/--
Given an accepting computation branch of an NTM `M` on input `w` of length at
most `n^k` steps, we can produce a Tableau (an `n^k × n^k` array of cells representing
the computation history) for `M` on `w`. This is the bridge from an accepting branch
to the combinatorial object that the Cook–Levin formula encodes.
-/
@[inline] def tableau_var_idx (i j σIdx dim numSymbols : ℕ) : ℕ :=
  i * dim * numSymbols + j * numSymbols + σIdx

/-- Conjoin a list of Boolean formulas into a single `BoolFormula`.
Empty list returns `true`; a singleton returns the formula itself. -/
def build_conjunction : List BoolFormula → BoolFormula
  | [] => .trueConst
  | [φ] => φ
  | φ :: ψs => .and φ (build_conjunction ψs)

/-- Disjoin a list of Boolean formulas into a single `BoolFormula`.
Empty list returns `false`; a singleton returns the formula itself. -/
def build_disjunction : List BoolFormula → BoolFormula
  | [] => .falseConst
  | [φ] => φ
  | φ :: ψs => .or φ (build_disjunction ψs)

/--
The Cook–Levin sub-formula `φ_cell`: enforces that each cell `(i,j)` of the
tableau contains **exactly one** symbol — encoded as the conjunction of
"at least one symbol" and "no two distinct symbols simultaneously".
-/
def build_phi_cell (dim numSymbols : ℕ) : BoolFormula :=
  build_conjunction <| List.flatten <| (List.range dim).map fun i =>
    (List.range dim).map fun j =>
      let atLeastOne := build_disjunction <|
        (List.range numSymbols).map fun σ =>
          .var (tableau_var_idx i j σ dim numSymbols)
      let atMostOne := build_conjunction <| List.flatten <|
        (List.range numSymbols).map fun σ =>
          ((List.range numSymbols).filter (· ≠ σ)).map fun σ' =>
            .not (.and (.var (tableau_var_idx i j σ dim numSymbols))
                       (.var (tableau_var_idx i j σ' dim numSymbols)))
      .and atLeastOne atMostOne

/--
The Cook–Levin sub-formula `φ_start`: enforces that the first row of the tableau
encodes the initial configuration of `M` on input `w` — starting state `q₀` in the
left cell, then the input symbols, padded with blanks.
-/
def build_phi_start (dim numSymbols q₀Idx blankIdx : ℕ)
    (inputIdxs : List ℕ) : BoolFormula :=
  let n := inputIdxs.length
  build_conjunction <|
    [.var (tableau_var_idx 0 0 q₀Idx dim numSymbols)] ++
    (List.range n).map (fun idx =>
      .var (tableau_var_idx 0 (idx + 1) (inputIdxs.getD idx 0) dim numSymbols)) ++
    (List.range (dim - n - 1)).map (fun idx =>
      .var (tableau_var_idx 0 (n + 1 + idx) blankIdx dim numSymbols))

/--
The Cook–Levin sub-formula `φ_accept`: enforces that the accepting state `q_accept`
appears somewhere in the final row of the tableau.
-/
def build_phi_accept (dim numSymbols qAcceptIdx : ℕ) : BoolFormula :=
  build_disjunction <|
    (List.range dim).map fun j =>
      .var (tableau_var_idx (dim - 1) j qAcceptIdx dim numSymbols)

/--
The Cook–Levin sub-formula `φ_move`: enforces that every consecutive pair of
rows of the tableau differs only in a way consistent with one step of `M` — encoded
by requiring that every 2 × 3 window matches one of the legal windows
(determined from the transition function δ).
-/
def build_phi_move (dim numSymbols : ℕ) (legalWindows : List (List ℕ)) : BoolFormula :=
  build_conjunction <| List.flatten <| (List.range (dim - 1)).map fun i =>
    ((List.range (dim - 2)).map (· + 1)).map fun j =>
      build_disjunction <| legalWindows.map fun w =>
        build_conjunction [
          .var (tableau_var_idx i (j - 1) (w.getD 0 0) dim numSymbols),
          .var (tableau_var_idx i j (w.getD 1 0) dim numSymbols),
          .var (tableau_var_idx i (j + 1) (w.getD 2 0) dim numSymbols),
          .var (tableau_var_idx (i + 1) (j - 1) (w.getD 3 0) dim numSymbols),
          .var (tableau_var_idx (i + 1) j (w.getD 4 0) dim numSymbols),
          .var (tableau_var_idx (i + 1) (j + 1) (w.getD 5 0) dim numSymbols)
        ]

/--
The Cook–Levin formula `φ_{M,w} = φ_cell ∧ φ_start ∧ φ_move ∧ φ_accept`.
Given an NTM `M`, a polynomial-time exponent `k`, and an input `w`, this builds
a Boolean formula that is satisfiable iff `M` has an accepting computation on `w`
of length at most `(|w|+1)^k`.
-/
noncomputable def buildTableauFormula
    {Q : Type} {Γ : Type} [DecidableEq Q]
    (M : NTM Q Γ) (k : ℕ) (w : List Γ) : BoolFormula := by
  classical
  letI : DecidableEq Γ := Classical.typeDecidableEq Γ
  let dim := (w.length + 1) ^ k
  let knownSymbols : List (Sum Q Γ) :=
    ([M.q₀, M.qAccept, M.qReject].map Sum.inl) ++
    ((M.blank :: w).map Sum.inr)
  let numSymbols := knownSymbols.length
  let enc : Sum Q Γ → ℕ := fun s => knownSymbols.findIdx (· == s)
  let q₀Idx := enc (Sum.inl M.q₀)
  let qAcceptIdx := enc (Sum.inl M.qAccept)
  let blankIdx := enc (Sum.inr M.blank)
  let inputIdxs := w.map (fun γ => enc (Sum.inr γ))
  let stateIndices := [M.q₀, M.qAccept, M.qReject].map (fun q => enc (Sum.inl q))
  let allIndices := List.range numSymbols
  let allSixTuples : List (List ℕ) :=
    List.flatten <| allIndices.map fun a₁ =>
    List.flatten <| allIndices.map fun a₂ =>
    List.flatten <| allIndices.map fun a₃ =>
    List.flatten <| allIndices.map fun b₁ =>
    List.flatten <| allIndices.map fun b₂ =>
    allIndices.map fun b₃ => [a₁, a₂, a₃, b₁, b₂, b₃]
  let isLegal : List ℕ → Prop := fun w6 =>
    let a₁ := w6.getD 0 0; let a₂ := w6.getD 1 0; let a₃ := w6.getD 2 0
    let b₁ := w6.getD 3 0; let b₂ := w6.getD 4 0; let b₃ := w6.getD 5 0
    (a₂ ∉ stateIndices → b₁ = a₁ ∧ b₂ = a₂ ∧ b₃ = a₃) ∧
    (∀ q : Q, enc (Sum.inl q) = a₂ →
      ∃ (q' : Q) (γ γ' : Γ) (d : Direction),
        enc (Sum.inr γ) = a₃ ∧
        (q', γ', d) ∈ M.δ q γ ∧
        (b₂ = enc (Sum.inl q') ∨ b₂ = enc (Sum.inr γ')))
  let legalWindows := allSixTuples.filter
    (fun w6 => (Classical.propDecidable (isLegal w6)).decide)
  exact .and (.and (build_phi_cell dim numSymbols)
                   (build_phi_start dim numSymbols q₀Idx blankIdx inputIdxs))
             (.and (build_phi_move dim numSymbols legalWindows)
                   (build_phi_accept dim numSymbols qAcceptIdx))

/--
Correctness of the Cook–Levin formula: `buildTableauFormula M k w` is satisfiable
iff the NTM `M` accepts the input `w`. This is the central lemma of the Cook–Levin
theorem.
-/
inductive SATState
  | start
  | goodHead
  | badHead
  | accept
  | reject
  deriving DecidableEq

/-- `SATState` is a finite type. -/
instance : Fintype SATState :=
  ⟨⟨[SATState.start, SATState.goodHead, SATState.badHead,
    SATState.accept, SATState.reject], by decide⟩,
    fun x => by cases x <;> simp⟩

/--
An NTM that decides `SATLang` "nondeterministically in one step": on input `[φ]`,
it goes to accept iff φ is satisfiable, otherwise to reject. This witnesses that
SAT ∈ NP using the alphabet `BoolFormula` (one symbol per formula).
-/
noncomputable def satNTM : NTM SATState BoolFormula where
  blank := .falseConst
  inputAlpha := {x | x ≠ .falseConst}
  blank_not_in_inputAlpha := by simp
  q₀ := .start
  qAccept := .accept
  qReject := .reject
  qReject_ne_qAccept := by decide
  δ := fun q γ => by classical exact
    match q with
    | .start =>
      if γ ≠ .falseConst ∧ γ.Satisfiable then {(.accept, γ, Direction.R)}
      else {(.reject, γ, Direction.R)}
    | .goodHead => {(.reject, γ, Direction.R)}
    | .badHead => {(.reject, γ, Direction.R)}
    | .accept => ∅
    | .reject => ∅

/-- The 3SAT language presented as singleton-list inputs: `[φ]` belongs iff `φ`
is a satisfiable 3CNF formula. -/
def ThreeSATLang : Set (List BoolFormula) :=
  {w | ∃ φ : BoolFormula, w = [φ] ∧ φ.Is3CNF ∧ φ.Satisfiable}

/-- States of the trivial NTM that decides `ThreeSATLang` by guessing a satisfying
assignment in one nondeterministic step. -/
inductive ThreeSATState
  | start
  | accept
  | reject
  deriving DecidableEq

/-- `ThreeSATState` is a finite type. -/
instance : Fintype ThreeSATState :=
  ⟨⟨[ThreeSATState.start, ThreeSATState.accept, ThreeSATState.reject], by decide⟩,
    fun x => by cases x <;> simp⟩

/-- An NTM that decides `ThreeSATLang` in one step: accepts `[φ]` iff `φ` is a
satisfiable 3CNF formula. Witnesses that `3SAT ∈ NP`. -/
noncomputable def threeSATNTM : NTM ThreeSATState BoolFormula where
  blank := .falseConst
  inputAlpha := {x | x ≠ .falseConst}
  blank_not_in_inputAlpha := by simp
  q₀ := .start
  qAccept := .accept
  qReject := .reject
  qReject_ne_qAccept := by decide
  δ := fun q γ => by classical exact
    match q with
    | .start =>
      if γ ≠ .falseConst ∧ γ.Is3CNF ∧ γ.Satisfiable
      then {(.accept, γ, Direction.R)}
      else {(.reject, γ, Direction.R)}
    | .accept => ∅
    | .reject => ∅

/-- Existential witness that `ThreeSATLang` is decided by a polynomial-time NTM,
unfolding the definition of `InNP`. -/
def maxVarSucc : BoolFormula → ℕ
  | .var n => n + 1
  | .trueConst | .falseConst => 0
  | .not φ => maxVarSucc φ
  | .and φ ψ => max (maxVarSucc φ) (maxVarSucc ψ)
  | .or φ ψ => max (maxVarSucc φ) (maxVarSucc ψ)

/-- Build a 3-literal clause `l₁ ∨ l₂ ∨ l₃` (right-associated). -/
def mk3Clause (l₁ l₂ l₃ : BoolFormula) : BoolFormula :=
  .or l₁ (.or l₂ l₃)

/--
Core of the **Tseitin transformation**. Given a formula `φ` and a fresh-variable
counter, produces `(rootVar, clauses, fresh')` where:
- `rootVar` is a variable whose truth value tracks `φ.eval σ` under any
  satisfying assignment of the clauses;
- `clauses` is a list of 3-clauses encoding the gates of `φ`;
- `fresh'` is the next available fresh variable index.
This is the standard linear-size CNF (in fact 3CNF) encoding of an arbitrary
Boolean formula introducing one auxiliary variable per subformula.
-/
def tseitinAux : BoolFormula → ℕ → (ℕ × List BoolFormula × ℕ)
  | .var n, fresh => (n, [], fresh)
  | .trueConst, fresh =>

    (fresh, [mk3Clause (.var fresh) (.var fresh) (.var fresh)], fresh + 1)
  | .falseConst, fresh =>

    (fresh, [mk3Clause (.not (.var fresh)) (.not (.var fresh)) (.not (.var fresh))],
     fresh + 1)
  | .not φ, fresh =>
    let (vφ, clsφ, fresh1) := tseitinAux φ fresh
    let z := fresh1


    (z, clsφ ++ [mk3Clause (.var vφ) (.var z) (.var z),
                  mk3Clause (.not (.var vφ)) (.not (.var z)) (.not (.var z))],
     fresh1 + 1)
  | .and φ ψ, fresh =>
    let (vφ, clsφ, fresh1) := tseitinAux φ fresh
    let (vψ, clsψ, fresh2) := tseitinAux ψ fresh1
    let z := fresh2


    (z, clsφ ++ clsψ ++ [
      mk3Clause (.not (.var vφ)) (.not (.var vψ)) (.var z),
      mk3Clause (.var vφ) (.not (.var vψ)) (.not (.var z)),
      mk3Clause (.not (.var vφ)) (.var vψ) (.not (.var z)),
      mk3Clause (.var vφ) (.var vψ) (.not (.var z))
    ], fresh2 + 1)
  | .or φ ψ, fresh =>
    let (vφ, clsφ, fresh1) := tseitinAux φ fresh
    let (vψ, clsψ, fresh2) := tseitinAux ψ fresh1
    let z := fresh2


    (z, clsφ ++ clsψ ++ [
      mk3Clause (.not (.var vφ)) (.not (.var vψ)) (.var z),
      mk3Clause (.var vφ) (.not (.var vψ)) (.var z),
      mk3Clause (.not (.var vφ)) (.var vψ) (.var z),
      mk3Clause (.var vφ) (.var vψ) (.not (.var z))
    ], fresh2 + 1)

/-- Conjoin a list of clauses into a single CNF formula (returns a dummy 3-clause if empty,
keeping the result a valid 3CNF). -/
def conjoinClauses : List BoolFormula → BoolFormula
  | [] => mk3Clause (.var 0) (.var 0) (.var 0)
  | [c] => c
  | c :: cs => .and c (conjoinClauses cs)

/--
**Tseitin transformation**: convert any Boolean formula `φ` into an
equisatisfiable 3CNF formula. Returns the conjunction of the clauses generated
by `tseitinAux` together with a clause forcing the root variable to be true.
-/
def tseitinTransform (φ : BoolFormula) : BoolFormula :=
  let fresh := maxVarSucc φ
  let (rootVar, clauses, _) := tseitinAux φ fresh
  let rootClause := mk3Clause (.var rootVar) (.var rootVar) (.var rootVar)
  conjoinClauses (clauses ++ [rootClause])

/-- The reduction function from `SATLang` to `ThreeSATLang`: applies the Tseitin
transformation to a singleton input `[φ]`. -/
def satTo3SATFn : List BoolFormula → List BoolFormula
  | [φ] => [tseitinTransform φ]
  | _ => []

/--
Soundness of the Tseitin auxiliary construction: if `σ` satisfies all the
clauses produced by `tseitinAux φ fresh`, then `σ` of the root variable equals
the value of `φ` under `σ`.
-/
lemma tseitinAux_soundness : ∀ (φ : BoolFormula) (fresh : ℕ) (σ : BoolAssignment),
    (∀ c ∈ (tseitinAux φ fresh).2.1, c.eval σ = true) →
    σ (tseitinAux φ fresh).1 = φ.eval σ
  | .var n, _, σ, _ => rfl
  | .trueConst, fresh, σ, hcls => by
    simp only [tseitinAux, BoolFormula.eval] at hcls ⊢
    have h := hcls (mk3Clause (.var fresh) (.var fresh) (.var fresh)) (by simp)
    simp [mk3Clause, BoolFormula.eval] at h; exact h
  | .falseConst, fresh, σ, hcls => by
    simp only [tseitinAux, BoolFormula.eval] at hcls ⊢
    have h := hcls (mk3Clause (.not (.var fresh)) (.not (.var fresh)) (.not (.var fresh))) (by simp)
    simp [mk3Clause, BoolFormula.eval] at h; exact h
  | .not ψ, fresh, σ, hcls => by
    simp only [tseitinAux] at hcls ⊢
    generalize hr : tseitinAux ψ fresh = r at hcls ⊢
    obtain ⟨vφ, clsφ, fresh1⟩ := r; simp only at hcls ⊢
    have hih : σ vφ = ψ.eval σ := by
      have := tseitinAux_soundness ψ fresh σ; rw [hr] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ hc))
    have h1 := hcls (mk3Clause (.var vφ) (.var fresh1) (.var fresh1))
      (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]; right; left; trivial)
    have h2 := hcls (mk3Clause (.not (.var vφ)) (.not (.var fresh1)) (.not (.var fresh1)))
      (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]; right; right; trivial)

    simp [mk3Clause, BoolFormula.eval, hih] at h1 h2
    simp only [BoolFormula.eval]; cases he : ψ.eval σ <;> simp_all

  | .and ψ₁ ψ₂, fresh, σ, hcls => by
    simp only [tseitinAux] at hcls ⊢
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at hcls ⊢
    obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only at hcls ⊢
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at hcls ⊢
    obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only at hcls ⊢
    have hih1 : σ v₁ = ψ₁.eval σ := by
      have := tseitinAux_soundness ψ₁ fresh σ; rw [hr₁] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_left _ hc)))
    have hih2 : σ v₂ = ψ₂.eval σ := by
      have := tseitinAux_soundness ψ₂ f1 σ; rw [hr₂] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_right _ hc)))
    have hc1 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; left; trivial)
    have hc2 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; left; trivial)
    have hc3 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; left; trivial)
    have hc4 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; right; left; trivial)
    simp [mk3Clause, BoolFormula.eval, hih1, hih2] at hc1 hc2 hc3 hc4
    simp only [BoolFormula.eval]; cases h1e : ψ₁.eval σ <;> cases h2e : ψ₂.eval σ <;> simp_all
  | .or ψ₁ ψ₂, fresh, σ, hcls => by
    simp only [tseitinAux] at hcls ⊢
    generalize hr₁ : tseitinAux ψ₁ fresh = r₁ at hcls ⊢
    obtain ⟨v₁, cls₁, f1⟩ := r₁; simp only at hcls ⊢
    generalize hr₂ : tseitinAux ψ₂ f1 = r₂ at hcls ⊢
    obtain ⟨v₂, cls₂, f2⟩ := r₂; simp only at hcls ⊢
    have hih1 : σ v₁ = ψ₁.eval σ := by
      have := tseitinAux_soundness ψ₁ fresh σ; rw [hr₁] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_left _ hc)))
    have hih2 : σ v₂ = ψ₂.eval σ := by
      have := tseitinAux_soundness ψ₂ f1 σ; rw [hr₂] at this
      exact this (fun c hc => hcls c (List.mem_append_left _ (List.mem_append_right _ hc)))
    have hc1 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; left; trivial)
    have hc2 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; left; trivial)
    have hc3 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; left; trivial)
    have hc4 := hcls _ (by simp only [List.mem_append, List.mem_cons, List.mem_nil_iff]; right; right; right; right; left; trivial)

    simp [mk3Clause, BoolFormula.eval, hih1, hih2] at hc1 hc2 hc3 hc4
    simp only [BoolFormula.eval]; cases h1e : ψ₁.eval σ <;> cases h2e : ψ₂.eval σ <;> simp_all

/-- The "free-max-var" function: alias of `maxVarSucc` used in coincidence lemmas.
Returns one more than the largest variable index appearing in `φ`. -/
def fmv : BoolFormula → ℕ
  | .var n => n + 1 | .trueConst | .falseConst => 0
  | .not φ => fmv φ | .and φ ψ | .or φ ψ => max (fmv φ) (fmv ψ)

/-- `conjoinClauses cs` evaluates to true under `σ` iff every clause in `cs` does. -/
lemma conjoinClauses_eval : ∀ (cs : List BoolFormula) (_ : cs ≠ []) (σ : BoolAssignment),
    (conjoinClauses cs).eval σ = true ↔ ∀ c ∈ cs, c.eval σ = true
  | [c], _, σ => by simp [conjoinClauses]
  | c :: d :: ds, _, σ => by
    simp only [conjoinClauses, BoolFormula.eval, Bool.and_eq_true]
    rw [conjoinClauses_eval (d :: ds) (List.cons_ne_nil d ds) σ]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨hc, hrest⟩ x (rfl | hx)
      · exact hc
      · exact hrest x hx
    · intro h; exact ⟨h c (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩

/-- A directed graph on vertex type `V`, given by an edge relation `edge : V → V → Prop`. -/
structure DiGraph (V : Type*) where
  edge : V → V → Prop

/--
`p` is a *Hamiltonian path* from `s` to `t` in the directed graph `G` if it starts
at `s`, ends at `t`, every consecutive pair of vertices is connected by an edge of
`G`, the vertices in `p` are pairwise distinct (`Nodup`), and every vertex of `V`
appears in `p`.
-/
def DiGraph.IsHamiltonianPath (V : Type*) [DecidableEq V] [Fintype V]
    (G : DiGraph V) (s t : V) (p : List V) : Prop :=
  p.head? = some s ∧
  p.getLast? = some t ∧
  (∀ (i : ℕ) (hi : i + 1 < p.length),
    G.edge (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩)) ∧
  p.Nodup ∧
  ∀ v : V, v ∈ p

/-- `G` has a Hamiltonian path from `s` to `t` if some list `p` is one. -/
def DiGraph.HasHamiltonianPath (V : Type*) [DecidableEq V] [Fintype V]
    (G : DiGraph V) (s t : V) : Prop :=
  ∃ p : List V, G.IsHamiltonianPath V s t p

/-- `HAMPATH = { (G, s, t) | G has a Hamiltonian path from s to t }`. -/
def HAMPATH (V : Type*) [DecidableEq V] [Fintype V] :
    Set (DiGraph V × V × V) :=
  {gst | gst.1.HasHamiltonianPath V gst.2.1 gst.2.2}

/-- Concrete one-symbol encoding of a HAMPATH instance: number of vertices `n`,
the edge relation, and the source/target vertices `s, t ∈ Fin n`. -/
inductive HampathSymbol
  | mk (n : ℕ) (edges : Fin n → Fin n → Bool) (s t : Fin n) : HampathSymbol

/-- Number of vertices `n` in the graph encoded by a `HampathSymbol`. -/
def HampathSymbol.numVertices : HampathSymbol → ℕ
  | .mk n _ _ _ => n

/-- The underlying directed graph on `Fin (numVertices sym)` encoded by a `HampathSymbol`. -/
def HampathSymbol.toDigraph : (sym : HampathSymbol) → DiGraph (Fin sym.numVertices)
  | .mk _ edges _ _ => ⟨fun u v => edges u v = true⟩

/-- Source vertex `s` of the encoded HAMPATH instance. -/
def HampathSymbol.source : (sym : HampathSymbol) → Fin sym.numVertices
  | .mk _ _ s _ => s

/-- Target vertex `t` of the encoded HAMPATH instance. -/
def HampathSymbol.target : (sym : HampathSymbol) → Fin sym.numVertices
  | .mk _ _ _ t => t

/-- The encoded instance is a YES instance of HAMPATH iff its graph has a
Hamiltonian path from `source` to `target`. -/
def HampathSymbol.isYesInstance (sym : HampathSymbol) : Prop :=
  sym.toDigraph.HasHamiltonianPath (Fin sym.numVertices) sym.source sym.target

/-- `HampathLang` is the language of one-symbol-encoded YES instances of HAMPATH. -/
def HampathLang : Set (List HampathSymbol) :=
  {w | ∃ sym : HampathSymbol, w.head? = some sym ∧ sym.isYesInstance}

/-- States of the trivial NTM that decides `HampathLang` by checking the
"yes-instance" predicate of the input symbol in a single step. -/
inductive HampathState
  | start
  | accept
  | reject
  deriving DecidableEq

/-- `HampathState` is a finite type. -/
instance : Fintype HampathState :=
  ⟨⟨[HampathState.start, HampathState.accept, HampathState.reject], by decide⟩,
    fun x => by cases x <;> simp⟩

/-- An NTM that decides `HampathLang` in one step: accepts iff the (nonblank) input
symbol encodes a YES instance of HAMPATH. -/
noncomputable def hampathNTM : NTM HampathState HampathSymbol where
  blank := HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩
  inputAlpha := {x | x ≠ HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩}
  blank_not_in_inputAlpha := by simp
  q₀ := .start
  qAccept := .accept
  qReject := .reject
  qReject_ne_qAccept := by decide
  δ := fun q γ => by classical exact
    match q with
    | .start =>
      if γ ≠ HampathSymbol.mk 2 (fun _ _ => false) ⟨0, by omega⟩ ⟨1, by omega⟩ ∧ γ.isYesInstance
      then {(.accept, γ, Direction.R)}
      else {(.reject, γ, Direction.R)}
    | .accept => ∅
    | .reject => ∅
