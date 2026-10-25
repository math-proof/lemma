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
import Abbrev.v1.Atlas.TheoryOfComputation.code.NPCompleteness


namespace NPCompleteness

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

end NPCompleteness
