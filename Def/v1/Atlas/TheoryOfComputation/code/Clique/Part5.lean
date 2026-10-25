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
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.NPCompleteness
import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part8
import Abbrev.v1.Atlas.TheoryOfComputation.code.Clique.Part2


namespace ThreeSATToClique

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

end ThreeSATToClique
