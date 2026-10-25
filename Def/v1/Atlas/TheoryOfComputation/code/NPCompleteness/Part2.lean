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
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Structure.v1.Atlas.TheoryOfComputation.code.Tableau
import Theorem.v1.Atlas.TheoryOfComputation.code.NPCompleteness


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

end CookLevin
