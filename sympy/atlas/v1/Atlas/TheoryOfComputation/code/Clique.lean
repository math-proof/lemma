/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NPCompleteness
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.NPCompleteness

namespace Clique

open SimpleGraph

/-- A graph `G` has a `k`-clique iff there exists a `k`-vertex subset all of
whose pairs are adjacent in `G`. -/
def HasKClique {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (s : Finset V), G.IsNClique k s

/-- The language `CLIQUE = {⟨G, k⟩ | G has a k-clique}` as a set of
graph/integer pairs. -/
def CLIQUE (V : Type*) : Set (SimpleGraph V × ℕ) :=
  {p | HasKClique p.1 p.2}

end Clique

namespace ThreeSATToClique

/-- The polarity of a propositional literal: positive (`x`) or negative (`¬x`). -/
inductive Polarity where
  | pos : Polarity
  | neg : Polarity
  deriving DecidableEq, Repr

/-- A propositional literal: a variable index together with a polarity, so
that `⟨i, .pos⟩` represents `x_i` and `⟨i, .neg⟩` represents `¬x_i`. -/
structure Literal where
  varIdx : ℕ
  pol : Polarity
  deriving DecidableEq, Repr

/-- Two literals are contradictory when they refer to the same variable but
have opposite polarities (e.g. `x_i` and `¬x_i`). -/
def Literal.IsContradictory (l₁ l₂ : Literal) : Prop :=
  l₁.varIdx = l₂.varIdx ∧ l₁.pol ≠ l₂.pol

/-- Contradictoriness of literals is decidable, inherited from decidability of
equality on variable indices and polarities. -/
instance (l₁ l₂ : Literal) : Decidable (l₁.IsContradictory l₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Evaluate a literal under a truth assignment `σ : ℕ → Bool`: a positive
literal returns `σ l.varIdx`, a negative literal returns its negation. -/
def Literal.eval (σ : ℕ → Bool) (l : Literal) : Bool :=
  match l.pol with
  | .pos => σ l.varIdx
  | .neg => !σ l.varIdx

/-- A 3-clause is a triple of literals, representing the disjunction
`l₁ ∨ l₂ ∨ l₃` in a 3CNF formula. -/
abbrev ThreeClause := Literal × Literal × Literal

/-- Project the `j`-th literal (for `j : Fin 3`) out of a 3-clause. -/
def ThreeClause.literalAt (c : ThreeClause) (j : Fin 3) : Literal :=
  match j with
  | ⟨0, _⟩ => c.1
  | ⟨1, _⟩ => c.2.1
  | ⟨2, _⟩ => c.2.2

/-- A 3-clause is satisfied by an assignment `σ` iff at least one of its three
literals evaluates to `true` under `σ`. -/
def ThreeClause.isSatBy (σ : ℕ → Bool) (c : ThreeClause) : Prop :=
  ∃ j : Fin 3, (c.literalAt j).eval σ = true

/-- A 3CNF formula, represented as a list of 3-clauses (interpreted as their
conjunction). -/
abbrev ThreeCNF := List ThreeClause

/-- A 3CNF formula `φ` is satisfiable iff there is an assignment `σ` under
which every clause of `φ` is satisfied. -/
def ThreeCNF.IsSatisfiable (φ : ThreeCNF) : Prop :=
  ∃ σ : ℕ → Bool, ∀ (i : Fin φ.length), (φ.get i).isSatBy σ

/-- The graph produced by the standard `3SAT ≤_P CLIQUE` reduction. Vertices
are pairs `(i, j)` with `i` a clause index and `j ∈ Fin 3` a literal position;
two distinct vertices are adjacent iff they come from different clauses and
their literals are not contradictory. A clique of size `|φ|` then encodes a
satisfying assignment by picking, in each clause, a literal that is true. -/
def reductionGraph (φ : ThreeCNF) :
    SimpleGraph (Fin φ.length × Fin 3) where
  Adj v₁ v₂ :=
    v₁ ≠ v₂ ∧
    v₁.1 ≠ v₂.1 ∧
    ¬((φ.get v₁.1).literalAt v₁.2).IsContradictory
      ((φ.get v₂.1).literalAt v₂.2)
  symm v₁ v₂ := by
    rintro ⟨hne, hcl, hnc⟩
    exact ⟨hne.symm, hcl.symm, fun h => hnc h.symm'⟩
  loopless := ⟨fun v ⟨hne, _, _⟩ => hne rfl⟩

/-- Given a satisfying assignment `σ` for a clause `c`, choose (using
classical choice) one position `j : Fin 3` whose literal evaluates to `true`. -/
noncomputable def ThreeClause.trueLitPos (σ : ℕ → Bool) (c : ThreeClause)
    (hsat : c.isSatBy σ) : Fin 3 :=
  hsat.choose

/-- Given a satisfying assignment `σ` for every clause of `φ`, build the
candidate clique in `reductionGraph φ` by selecting, for each clause `i`, the
vertex `(i, j)` where `j` is a position witnessing the clause's satisfaction. -/
noncomputable def satisfyingClique (φ : ThreeCNF) (σ : ℕ → Bool)
    (hsat : ∀ (i : Fin φ.length), (φ.get i).isSatBy σ) :
    Finset (Fin φ.length × Fin 3) :=
  Finset.univ.image (fun i => (i, (φ.get i).trueLitPos σ (hsat i)))

/-- Tape alphabet used to encode either a 3SAT instance or a CLIQUE instance
on a single Turing-machine tape. The symbol `sat φ` represents an encoded
3CNF formula `φ`, and `clique φ` represents the encoded CLIQUE instance
`⟨reductionGraph φ, |φ|⟩`. -/
inductive SATCliqueSymbol where
  | sat (φ : ThreeCNF) : SATCliqueSymbol
  | clique (φ : ThreeCNF) : SATCliqueSymbol

/-- Encoded 3SAT language: those single-symbol tape strings `[.sat φ]` whose
underlying formula `φ` is satisfiable. -/
def ThreeSATEnc : Set (List SATCliqueSymbol) :=
  {w | ∃ φ : ThreeCNF, w = [.sat φ] ∧ φ.IsSatisfiable}

/-- Encoded CLIQUE language (specialized to instances arising from the
reduction): the single-symbol strings `[.clique φ]` whose reduction graph
`reductionGraph φ` contains a `|φ|`-clique. -/
def CLIQUEEnc : Set (List SATCliqueSymbol) :=
  {w | ∃ (φ : ThreeCNF),
    w = [.clique φ] ∧ Clique.HasKClique (reductionGraph φ) φ.length}

/-- The reduction function `f : Σ* → Σ*` on encodings: maps `[.sat φ]` to
`[.clique φ]` and every other input to the empty string. -/
def threeSATToCliqueEnc : List SATCliqueSymbol → List SATCliqueSymbol
  | [.sat φ] => [.clique φ]
  | _ => []
